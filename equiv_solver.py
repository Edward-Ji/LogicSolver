"""
A very finicky logic equivalence solver.
"""

import math
import os
import sys
from collections import namedtuple
from itertools import product

from pyparsing.exceptions import ParseException

from logic_parser import (
    TOP, BOT, LNOT, LAND, LOR, IMPLIES, LRARR,
    is_verum, is_falsem, is_neg, is_conj, is_disj, is_imply, is_lrarr,
    parse_equiv, standardize, stringify
)
from table_format import print_table


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
        yield ((left, IMPLIES, right), LRARR, (right, IMPLIES, left))


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


def apply_laws_to_leaves(paths, nest_limit, path_len):
    new_paths = {}
    for path in paths.values():
        if len(path) < path_len:
            continue
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
            new_paths = apply_laws_to_leaves(left_paths,
                                             left_nest_limit,
                                             count // 2)
        else:
            new_paths = apply_laws_to_leaves(right_paths,
                                             right_nest_limit,
                                             count // 2)
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
            met_at, *_ = met
            left_path = left_paths[met_at]
            right_path = right_paths[met_at]
            right_formulas = [step.formula for step in right_path]
            right_laws = [step.law for step in right_path]
            fixed_path = [Step(formula, law) for formula, law in
                zip(right_formulas[-2::-1], right_laws[:0:-1])
            ]
            return left_path + fixed_path
        count += 1


def display_steps(steps):
    table = []
    for index, (formula, law) in enumerate(steps):
        index_str = str(index)
        formula_str = stringify(formula)
        table.append((index_str, formula_str, law))
    print_table(table, aligns=">^<", header=["Step", "Formula", "Law"])


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

    proof = prove_equiv(lhs, rhs)
    if proof is not None:
        print("Proof:")
        display_steps(proof)
    else:
        print("Failed to construct a proof.")


if __name__ == "__main__":
    sys.exit(main())
