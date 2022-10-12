"""
A very finicky logic equivalence solver.
"""

import math
import os
import sys
from collections import namedtuple
from itertools import product

import pyparsing
from pyparsing import (
    Char, Keyword, Literal, OpAssoc,
    alphas, infix_notation, one_of
)
from pyparsing.exceptions import ParseException


pyparsing.ParserElement.enablePackrat()

TOP = "⊤"
BOT = "⊥"
LNOT = "¬"
LAND = "∧"
LOR = "∨"
IMPLIES = "→"
LRARR = "↔"

not_ = Keyword("not", caseless=True)
and_ = Keyword("and", caseless=True)
or_ = Keyword("or", caseless=True)
implies_ = Keyword("implies", caseless=True)

verum = one_of(TOP + " 1")
falsem = one_of(BOT + " 0")
const = verum | falsem
var = Char(alphas)
atom = const | var

neg = one_of(LNOT + " ! ~") | not_
conj = one_of(LAND + " &") | and_
disj = one_of(LOR + " | +") | or_
imply = one_of(IMPLIES + " ->") | implies_
lrarr = one_of(LRARR + " <->")

expr = infix_notation(
    atom,
    [
        (neg, 1, OpAssoc.RIGHT),
        (conj, 2, OpAssoc.LEFT),
        (disj, 2, OpAssoc.LEFT),
        (imply, 2, OpAssoc.RIGHT),
        (lrarr, 2, OpAssoc.RIGHT)
    ]
)
equiv = expr + one_of("≡ ==") + expr



def parse_equiv(equiv_str):
    return equiv.parse_string(equiv_str, parse_all=True).as_list()


def is_verum(formula):
    return len(formula) == 1 and formula[0] == TOP


def is_falsem(formula):
    return len(formula) == 1 and formula[0] == BOT


def is_var(formula):
    return len(formula) == 1 and formula[0] not in (TOP, BOT)


def is_neg(formula):
    return len(formula) == 2


def is_conj(formula):
    return len(formula) == 3 and formula[1] == LAND


def is_disj(formula):
    return len(formula) == 3 and formula[1] == LOR


def is_imply(formula):
    return len(formula) == 3 and formula[1] == IMPLIES


def is_lrarr(formula):
    return len(formula) == 3 and formula[1] == LRARR


def idempotent_laws(formula):
    if is_conj(formula) or is_disj(formula):
        left, _, right = formula
        if left == right:
            yield left


def commutative_laws(formula):
    if is_conj(formula) or is_disj(formula):
        left, symbol, right = formula
        yield (right, symbol, left)


def associative_laws(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_conj(left):
            left_left, _, left_right = left
            yield (left_left, LAND, (left_right, LAND, right))
    elif is_disj(formula):
        left, _, right = formula
        if is_disj(left):
            left_left, _, left_right = left
            yield (left_left, LOR, (left_right, LOR, right))


def absorption_laws(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_disj(right):
            right_left, _, right_right = right
            if left == right_left:
                yield left
    elif is_disj(formula):
        left, _, right = formula
        if is_conj(right):
            right_left, _, right_right = right
            if left == right_left:
                yield left


def distributive_laws(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_disj(right):
            right_left, _, right_right = right
            yield ((left, LAND, right_left), LOR, (left, LAND, right_right))
    elif is_disj(formula):
        left, _, right = formula
        if is_conj(right):
            right_left, _, right_right = right
            yield ((left, LOR, right_left), LAND, (left, LOR, right_right))


def de_morgans_laws(formula):
    if is_neg(formula):
        _, right = formula
        if is_conj(right):
            right_left, _, right_right = right
            yield ((LNOT, right_left), LOR, (LNOT, right_right))
        if is_disj(right):
            right_left, _, right_right = right
            yield ((LNOT, right_left), LAND, (LNOT, right_right))


def double_negation_law(formula):
    if is_neg(formula):
        _, right = formula
        if is_neg(right):
            yield right[1]


def validity_law(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_verum(right):
            yield left
    if is_disj(formula):
        left, _, right = formula
        if is_verum(right):
            yield (TOP,)


def unsatisfiability_law(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_falsem(right):
            yield (BOT,)
    if is_disj(formula):
        left, _, right = formula
        if is_falsem(right):
            yield left


def constant_laws(formula):
    if is_conj(formula):
        left, _, right = formula
        if is_neg(right):
            _, right_right = right
            if left == right_right:
                yield (BOT,)
    elif is_disj(formula):
        left, _, right = formula
        if is_neg(right):
            _, right_right = right
            if left == right_right:
                yield (TOP,)


def negating_constant_laws(formula):
    if is_neg(formula):
        _, right = formula
        if is_verum(right):
            yield (BOT,)
        elif is_falsem(right):
            yield (TOP,)


def conditional_law(formula):
    if is_imply(formula):
        left, _, right = formula
        yield ((LNOT, left), LOR, right)


def bi_conditional_law(formula):
    if is_lrarr(formula):
        left, _, right = formula
        yield ((left, IMPLIES, right), LAND, (right, IMPLIES, left))


laws = {
    "Idempotent Laws": idempotent_laws,
    "Commutative Laws": commutative_laws,
    "Associative Laws": associative_laws,
    "Absorption Laws": absorption_laws,
    "Distributive Laws": distributive_laws,
    "de Morgan's Laws": de_morgans_laws,
    "Double Negation Law": double_negation_law,
    "Validity Law": validity_law,
    "Unsatisfiability Law": unsatisfiability_law,
    "Constant Laws": constant_laws,
    "Negating Constant Laws": negating_constant_laws,
    "Conditional Law": conditional_law,
    "Bi-conditional Law": bi_conditional_law
}


Step = namedtuple("Step", ["formula", "law"])


def apply_laws(formula):
    if len(formula) == 2:
        symbol, right = formula
        for right_applied, applied_law in apply_laws(right):
            yield Step((symbol, right_applied), applied_law)
    elif len(formula) == 3:
        left, symbol, right = formula
        for left_applied, applied_law in apply_laws(left):
            yield Step((left_applied, symbol, right), applied_law)
        for right_applied, applied_law in apply_laws(right):
            yield Step((left, symbol, right_applied), applied_law)
    for law_name, law in laws.items():
        for applied in law(formula):
            yield Step(applied, law_name)


def nest_level(formula):
    if len(formula) == 1:
        return 1
    elif len(formula) == 2:
        return nest_level(formula[1]) + 1
    else:
        return nest_level(formula[0]) + nest_level(formula[2]) + 1


def apply_laws_to_leaves(paths, nest_limit):
    new_paths = {}
    for path in paths.values():
        formula = path[-1].formula
        for new_step in apply_laws(formula):
            new_path = path + [new_step]
            applied = new_step.formula
            if applied not in paths and nest_level(applied) <= nest_limit:
                new_paths[applied] = new_path

    return new_paths


def prove_equiv(lhs, rhs, nest_limit=0):
    left_nest_limit = nest_limit or nest_level(lhs) + 5
    right_nest_limit = nest_limit or nest_level(rhs) + 5
    left_paths = {lhs: [Step(lhs, "Assumption Introduction")]}
    right_paths = {rhs: [Step(rhs, "")]}
    progress = True
    count = 1
    while count:
        print(f"Step {count}...")
        if count % 2:
            new_paths = apply_laws_to_leaves(left_paths, left_nest_limit)
        else:
            new_paths = apply_laws_to_leaves(right_paths, right_nest_limit)
        if not new_paths:
            if not progress:
                return
            progress = False
        else:
            print(f"\tFound {len(new_paths)} new paths.")
            progress = True
        if count % 2:
            left_paths.update(new_paths)
        else:
            right_paths.update(new_paths)
        met = left_paths.keys() & right_paths.keys()
        if met:
            for met_at in met:
                left_path = left_paths[met_at]
                right_path = right_paths[met_at]
                right_formulas = [step.formula for step in right_path]
                right_laws = [step.law for step in right_path]
                fixed_path = [Step(formula, law) for formula, law in
                    zip(right_formulas[-2::-1], right_laws[:0:-1])
                ]
                yield left_path + fixed_path
            return
        count += 1


def standardize(formula):
    if len(formula) == 1:
        if verum.matches(formula[0]):
            return (TOP,)
        elif falsem.matches(formula[0]):
            return (BOT,)
        elif var.matches(formula[0]):
            return (formula[0],)
        else:
            return standardize(formula[0])
    elif len(formula) == 2:
        return (LNOT, standardize(formula[1]))
    else:
        if conj.matches(formula[-2]):
            return (standardize(formula[:-2]), LAND, standardize(formula[-1]))
        elif disj.matches(formula[-2]):
            return (standardize(formula[:-2]), LOR, standardize(formula[-1]))
        elif imply.matches(formula[-2]):
            return (
                standardize(formula[:-2]), IMPLIES, standardize(formula[-1]))
        elif lrarr.matches(formula[-2]):
            return (standardize(formula[:-2]), LRARR, standardize(formula[-1]))


def stringify(formula):
    if is_verum(formula):
        return TOP
    elif is_falsem(formula):
        return BOT
    elif is_var(formula):
        return formula[0]
    elif is_neg(formula):
        right_str = stringify(formula[1])
        return f"{LNOT}{right_str}"
    elif len(formula) == 3:
        left_str = stringify(formula[0])
        right_str = stringify(formula[2])
        if is_conj(formula):
            return f"({left_str}{LAND}{right_str})"
        elif is_disj(formula):
            return f"({left_str}{LOR}{right_str})"
        elif is_imply(formula):
            return f"({left_str}{IMPLIES}{right_str})"
        elif is_lrarr(formula):
            return f"({left_str}{LRARR}{right_str})"


def display_steps(steps):
    index_width = math.ceil(math.log(len(steps)))
    table = []
    formula_width = 0
    for formula, law in steps:
        formula_str = stringify(formula)
        if len(formula_str) > formula_width:
            formula_width = len(formula_str)
        table.append((formula_str, law))
    for i, (formula_str, law) in enumerate(table):
        print(f"{i:{index_width}d} | {formula_str:^{formula_width}s} | {law}")


def main():
    print("Enter an equivalence: ")
    equiv_str = input()
    try:
        equiv_parsed = parse_equiv(equiv_str)
    except ParseException as err:
        print("Unable to parse:")
        print(equiv_str)
        print(f"{'^':>{err.col}s}")
        print(err)
        return 1

    lhs = standardize(equiv_parsed[0])
    rhs = standardize(equiv_parsed[2])

    print("Left hand side:", stringify(lhs))
    print("Right hand side:", stringify(rhs))

    proven = False
    for m, proof in enumerate(prove_equiv(lhs, rhs)):
        print(f"Proof {m}")
        display_steps(proof)
        proven = True
    if not proven:
        print("Failed to construct a proof.")


if __name__ == "__main__":
    sys.exit(main())
