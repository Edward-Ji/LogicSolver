import readline

import pyparsing
from pyparsing import (
    Char, Keyword, Literal, OpAssoc, Optional,
    alphas, delimited_list, infix_notation, one_of
)


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
condi = imply | lrarr

expr = infix_notation(
    atom,
    [
        (neg, 1, OpAssoc.RIGHT),
        (conj, 2, OpAssoc.LEFT),
        (disj, 2, OpAssoc.LEFT),
        (condi, 2, OpAssoc.RIGHT)
    ]
)

equiv = expr + one_of("≡ ==") + expr

deduce = Optional(delimited_list(expr)) + one_of("⊢ |-") + expr


def parse_equiv(equiv_str):
    return equiv.parse_string(equiv_str, parse_all=True).as_list()


def parse_deduce(deduce_str):
    return deduce.parse_string(deduce_str, parse_all=True).as_list()


def standardize(formula):
    if len(formula) == 1:
        if verum.matches(formula[0]):
            return (TOP,)
        elif falsem.matches(formula[0]):
            return (BOT,)
        elif var.matches(formula[0]):
            return (formula[0],)
        elif isinstance(formula[0], list):
            return standardize(formula[0])
        else:
            return (formula[0],)
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


def get_vars(formula):
    if len(formula) == 1:
        if is_var(formula):
            yield formula[0]
    elif len(formula) == 2:
        yield from get_vars(formula[1])
    elif len(formula) == 3:
        yield from get_vars(formula[0])
        yield from get_vars(formula[2])


def evaluate(formula, assignment):
    if is_verum(formula):
        return True
    elif is_falsem(formula):
        return False
    elif is_var(formula):
        return assignment[formula[0]]
    elif is_neg(formula):
        return not evaluate(formula[1], assignment)
    elif len(formula) == 3:
        left, _, right = formula
        if is_conj(formula):
            return evaluate(left, assignment) and evaluate(right, assignment)
        elif is_disj(formula):
            return evaluate(left, assignment) or evaluate(right, assignment)
        elif is_imply(formula):
            return not evaluate(left, assignment) or evaluate(right, assignment)
        elif is_lrarr(formula):
            return evaluate(left, assignment) == evaluate(right, assignment)


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
