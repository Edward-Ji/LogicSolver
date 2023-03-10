import os
import subprocess
import sys

from pyparsing import ParseException

from logic_parser import (
    alphas,
    is_verum, is_falsem, is_var, is_neg, is_conj, is_disj, is_imply, is_lrarr,
    parse_deduce, standardize, stringify, get_vars
)


def make_9y0(formula):
    if is_verum(formula):
        return "(Falsum --> Falsum)"
    if is_falsem(formula):
        return "Falsum"
    if is_var(formula):
        return f"Atom {alphas.index(formula[0])}"
    if is_neg(formula):
        right_str = make_9y0(formula[1])
        return f"({right_str} --> Falsum)"
    if len(formula) == 3:
        left_str = make_9y0(formula[0])
        right_str = make_9y0(formula[2])
        if is_conj(formula):
            return fr"({left_str} /\ {right_str})"
        if is_disj(formula):
            return fr"({left_str} \/ {right_str})"
        if is_imply(formula):
            return f"({left_str} --> {right_str})"
        if is_lrarr(formula):
            return (fr"({left_str} --> {right_str}) /\ "
                    fr"({left_str} <-- {right_str})")


def main():
    print("Enter a deductive sequence: ")
    deduce_str = input()
    try:
        deduce_parsed = parse_deduce(deduce_str)
    except ParseException as err:
        print("Unable to parse:")
        print(deduce_str)
        print(f"{'^':>{err.col}s}")
        print(err)
        return 1

    *assume_ls, _, conclude = map(standardize, deduce_parsed)
    vars = sorted({*get_vars(deduce_parsed)})

    for i, assume in enumerate(assume_ls, start=1):
        print(f"Assumption {i}:", stringify(assume))
    print("Conclusion:", stringify(conclude))

    command = ("import Formula\n"
               "sequence_ $ printDeductionTree <$> proofNK ({}) [{}]").format(
        make_9y0(conclude), ", ".join(map(make_9y0, assume_ls)))
    print("Command:", command)

    try:
        proc = subprocess.run(["ghci", "Main.hs"],
                              input=command,
                              capture_output=True, timeout=5, text=True)
    except FileNotFoundError as err:
        print(err)
        print("Error: check if you have Glasgow Haskell Compiler installed.")
        return 2
    except subprocess.TimeoutExpired:
        print("ghci command is taking too long")
        return 3


    tex_str = proc.stdout.split("ghci> ")[2]
    if not tex_str:
        print("Failed to construct a proof")
        return 3
    for var in vars:
        sub = str(alphas.index(var))
        if len(sub) == 1:
            tex_str = tex_str.replace(f"A_{sub}", var)
        else:
            tex_str = tex_str.replace(f"A_{{{sub}}}", var)

    with open("tmp.tex", "w") as tex:
        tex.write(
            r"""\documentclass{article}

\usepackage[a1paper, total={6in, 8in}]{geometry}
\usepackage{lkproof}
\usepackage{lscape}

\begin{document}
\begin{landscape}
            """)
        tex.write(tex_str)
        tex.write(r"""
\end{landscape}

\end{document}
        """)

    print("Successfully written to tmp.tex!")


if __name__ == "__main__":
    sys.exit(main())
