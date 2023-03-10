# LogicSolver
An automated logic equivalence and ND prover.

## Parser Syntax

```
verum  = "⊤" | "1"
falsum = "⊥" | "0"
const  = verum | falsum
var    = {A-Za-z}
atom   = const | var

neg    = ("¬" | "!" | "~" | "not") expr
conj   = expr ("∧" | "&" | "and") expr
disj   = expr ("∨" | "|" | "or") expr
imply  = expr ("→" | "->" | "implies") expr
lrarr  = expr ("↔" | "<->") expr
expr   = neg | conj | dist | implies | lrarr

equiv  = expr ("≡" | "==") expr
deduce = [expr "," ...] ("⊢" | "|-") expr
```

Operators by precedence from high to low and their associativity:

| Operation   | Associativity |
| ----------- | ------------- |
| neg         | right         |
| conj/disj   | left          |
| imply/lrarr | right         |

## Propositional Logic Equivalence Solver

Run `python equiv_solver.py` and enter an equivalence after the prompt.

```
Enter an equivalence: 
a == not not a
```

Then, the program will show you what it think both the left and right hand side
is, and what variables there are.

```
Left hand side: a
Left hand side (latex): a
Right hand side: ¬¬a
Variables: a
```

Next, it will check if the equivalence holds for all variable assignments. If
not, the program outputs an error message and aborts.

```
 | a | a | ¬¬a | 
 | - | - | --- | 
 | T | T |  T  | 
 | F | F |  F  | 
```

Then you'll have to wait a few seconds (or much longer) until it finds a proof.
The program shows the proof as a table in both markdown and LaTeX.

```
Step 1...
Step 2...
        Found 1 new paths.
Proof:
 | Step | Formula |           Law           | 
 | ---- | ------- | ----------------------- | 
 |    0 |    a    | Assumption Introduction | 
 |    1 |   ¬¬a   | Double Negation Law     | 
\begin{array}{|r|c|l|}
\text{Step} & \text{Formula} & \text{Law} \\
\hline
0 & a & \text{Assumption Introduction} \\
1 & \lnot \lnot a & \text{Double Negation Law} \\
\end{array}
```

## Natural Deduction Solver

This is a wrapper around [9Y0/NaturalDeduction]. Run the following command and
enter a deductive sequence.

```
python nd_solver.py
```

For example, a deductive sequence without any assumptions.

```
|- a -> not not a
```

Or another one with assumptions.

```
a |- b -> not not a
```

It outputs the assumptions and conclusion it think they are, and the Haskell
code it uses. The output will be in `tmp.tex`, you need to compile it using some
other tools.

[9Y0/NaturalDeduction]: https://github.com/9Y0/NaturalDeduction
