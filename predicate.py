# pylint: disable=missing-docstring
import readline  # pylint: disable=unused-import
import string
from collections import namedtuple
from dataclasses import dataclass

import pyparsing
from pyparsing import (
    Keyword, Literal, OpAssoc, Word,
    delimited_list, infix_notation, one_of
)
from pyparsing.exceptions import ParseBaseException, ParseFatalException

from table_format import print_table


pyparsing.ParserElement.enablePackrat()


@dataclass
class Variable:
    name: str
    bounded: bool = False


Constant = namedtuple("Constant", ["name"])
Predicate = namedtuple("Predicate", ["name", "vars"])
Negation = namedtuple("Negation", ["right"])
Conjunction = namedtuple("Conjunction", ["left", "right"])
Disjunction = namedtuple("Disjunction", ["left", "right"])
Implication = namedtuple("Implication", ["left", "right"])
BiImplication = namedtuple("BiImplication", ["left", "right"])
Forall = namedtuple("Forall", ["var", "right"])
Exists = namedtuple("Exists", ["var", "right"])

RED_BG = "\033[97;41m"
GREEN_BG = "\033[97;42m"
RESET = "\033[0m"

TOP = "⊤"
BOT = "⊥"
LNOT = "¬"
LAND = "∧"
LOR = "∨"
IMPLIES = "→"
LRARR = "↔"
FORALL = "∀"
EXISTS = "∃"
EQUIV = "≡"
LEFT_PAREN = Literal("(").suppress()
RIGHT_PAREN = Literal(")").suppress()

not_ = Keyword("not", caseless=True)
and_ = Keyword("and", caseless=True)
or_ = Keyword("or", caseless=True)
implies_ = Keyword("implies", caseless=True)
forall_ = Keyword("forall", caseless=True)
exists_ = Keyword("exist", caseless=True) | Keyword("exists", caseless=True)

verum = one_of(TOP + " 1")
verum.set_name("verum")
falsum = one_of(BOT + " 0")
falsum.set_name("falsum")
const = verum | falsum
const.set_name("constant")
var = Word(string.ascii_lowercase)
var.set_name("variable")
predicate = (Word(string.ascii_uppercase) + LEFT_PAREN + delimited_list(var, min=1)
             + RIGHT_PAREN)
predicate.set_name("predicate")
atom = const | predicate
atom.set_name("atom")

neg = one_of(LNOT + " ! ~") | not_
conj = one_of(LAND + " &") | and_
disj = one_of(LOR + " | +") | or_
imply = one_of(IMPLIES + " ->") | implies_
lrarr = one_of(LRARR + " <->")
condi = imply | lrarr

forall = one_of(FORALL) | forall_
exists = one_of(EXISTS) | exists_
forall_var = forall + var
exists_var = exists + var
quant = forall_var | exists_var

arity_map = {}


def get_predicates():
    strings = []
    for name, arity in arity_map.items():
        args = ", ".join(map(sorted(var.initChars).__getitem__, range(arity)))
        strings.append(f"{name}({args})")

    return " ".join(strings)


def const_action(toks):
    if verum.matches(toks[0]):
        return Constant(TOP)
    return Constant(BOT)


def predicate_action(line, loc, toks):
    name, *variables = toks
    if name in arity_map and arity_map[name] != len(variables):
        raise ParseFatalException(
            line, loc, f"Previous usage of {name} has arity {arity_map[name]}")
    arity_map[name] = len(variables)

    return Predicate(name, variables)


def condi_action(toks):
    left, ope, right = toks[0]
    if imply.matches(ope):
        return Implication(left, right)
    return BiImplication(left, right)


def mark_bounded(formula, var):
    if isinstance(formula, Predicate):
        for formula_var in formula.vars:
            if formula_var.name == var.name:
                formula_var.bounded = True
    if isinstance(formula, Negation):
        mark_bounded(formula.right, var)
    if (isinstance(formula, Conjunction)
            or isinstance(formula, Disjunction)
            or isinstance(formula, Implication)
            or isinstance(formula, BiImplication)):
        mark_bounded(formula.left, var)
        mark_bounded(formula.right, var)
    if isinstance(formula, Forall) or isinstance(formula, Exists):
        mark_bounded(formula.right, var)


def quant_action(toks):
    op, var, right = toks[0]
    mark_bounded(right, var)
    if forall.matches(op):
        return Forall(var, right)
    else:
        return Exists(var, right)


var.set_parse_action(lambda toks: Variable(toks[0], False))
const.set_parse_action(const_action)
predicate.set_parse_action(predicate_action)

expr = infix_notation(
    atom,
    [
        (quant, 1, OpAssoc.RIGHT, quant_action),
        (neg, 1, OpAssoc.RIGHT,
         lambda toks: Negation(toks[0][1])),
        (conj, 2, OpAssoc.LEFT,
         lambda toks: Conjunction(toks[0][0], toks[0][2])),
        (disj, 2, OpAssoc.LEFT,
         lambda toks: Disjunction(toks[0][0], toks[0][2])),
        (condi, 2, OpAssoc.RIGHT, condi_action)
    ]
)

equiv = expr + one_of(EQUIV + " ==") + expr


def parse_equiv(equiv_str):
    arity_map.clear()
    return equiv.parse_string(equiv_str, parse_all=True)


def stringify(formula, color_bounded=True):
    if isinstance(formula, Variable):
        if color_bounded:
            if formula.bounded:
                return f"{RED_BG}{formula.name}{RESET}"
            else:
                return f"{GREEN_BG}{formula.name}{RESET}"
        else:
            return formula.name
    if isinstance(formula, Constant):
        return formula.name
    if isinstance(formula, Predicate):
        vars_str = ",".join(map(lambda var: stringify(var, color_bounded),
                                 formula.vars))
        return f"{formula.name}({vars_str})"
    if hasattr(formula, "left"):
        left_str = stringify(formula.left, color_bounded)
    if hasattr(formula, "right"):
        right_str = stringify(formula.right, color_bounded)
    if isinstance(formula, Negation):
        return f"{LNOT}{right_str}"
    if isinstance(formula, Conjunction):
        return f"({left_str}{LAND}{right_str})"
    if isinstance(formula, Disjunction):
        return f"({left_str}{LOR}{right_str})"
    if isinstance(formula, Implication):
        return f"({left_str}{IMPLIES}{right_str})"
    if isinstance(formula, BiImplication):
        return f"({left_str}{LRARR}{right_str})"
    if isinstance(formula, Forall):
        return f"{FORALL}{formula.var.name}{right_str}"
    if isinstance(formula, Exists):
        return f"{EXISTS}{formula.var.name}{right_str}"


def idempotent_laws(formula):
    if isinstance(formula, Conjunction | Disjunction):
        if formula.left == formula.right:
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


def evaluate(formula, domain, predicate, assignment=None):
    if assignment is None:
        assignment = {}

    if isinstance(formula, Variable):
        assert False
    if isinstance(formula, Constant):
        return formula.name == TOP
    if isinstance(formula, Predicate):
        vars = tuple(assignment[var.name] for var in formula.vars)
        return vars in predicate[formula.name]
    if isinstance(formula, Negation):
        return not evaluate(formula.right, domain, predicate, assignment)
    if isinstance(formula, Conjunction):
        return (evaluate(formula.left, domain, predicate, assignment)
                and evaluate(formula.right, domain, predicate, assignment))
    if isinstance(formula, Disjunction):
        return (evaluate(formula.left, domain, predicate, assignment)
                or evaluate(formula.right, domain, predicate, assignment))
    if isinstance(formula, Implication):
        return (not evaluate(formula.left, domain, predicate, assignment)
                or evaluate(formula.right, domain, predicate, assignment))
    if isinstance(formula, BiImplication):
        return (evaluate(formula.left, domain, predicate, assignment)
                != evaluate(formula.right, domain, predicate, assignment))
    if isinstance(formula, Forall):
        for val in domain:
            assign_var = assignment | {formula.var.name: val}
            if not evaluate(formula.right, domain, predicate, assign_var):
                return False
        return True
    if isinstance(formula, Exists):
        for val in domain:
            assign_var = assignment | {formula.var.name: val}
            if evaluate(formula.right, domain, predicate, assign_var):
                return True
        return False


def main():
    print("Enter an equivalence: ")
    equiv_str = input()
    try:
        equiv_parsed = parse_equiv(equiv_str)
    except ParseBaseException as err:
        print("Unable to parse:")
        print(equiv_str)
        print(f"{'^':>{err.col}s}")
        print(err)
        return 1

    lhs = equiv_parsed[0]
    rhs = equiv_parsed[2]

    print("Left hand side:", stringify(lhs))
    print("Right hand side:", stringify(rhs))

    print("Predicates:", get_predicates())


if __name__ == "__main__":
    main()
