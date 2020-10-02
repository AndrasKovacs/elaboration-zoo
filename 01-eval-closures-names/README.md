
### elabzoo-eval-closures

Normalization-by-evaluation for untyped lambda calculus. Here we use explicit
closures to represent function values, that is, a function value is a value
environment packed together with the function body as a term.

This is esentially how all modern functional language compilers and interpreters
represent function objects at runtime: a captured environment of values together
with the program code for the function body.
