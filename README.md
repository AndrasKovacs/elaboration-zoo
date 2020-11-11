# elaboration-zoo

This repo includes a series of Haskell implementations for elaborating dependently typed languages, where packages add progressively more power and functionality. Currently, packages focus on basics of unification, inference and implicit argument handling, and we don't have any inductive types or modules (yet). 

Here are some [video recordings](https://www.youtube.com/playlist?list=PL2ZpyLROj5FOt99f_KCxARvd1hDqKns5b) from a seminar, covering some of the packages here plus additional topics. 

Work in progress. Each numbered directory contains a
[stack](https://docs.haskellstack.org/en/stable/README/) package. In each
directory, the `stack build` command builds the executable, `stack install`
additionally copies the executable to a PATH-visible `stack` folder, and `stack
ghci` can be used to load the package.

Generally, every package has a `main` function which takes some command line
flags and reads input from stdin, intended for command line usage, and a `main'`
function with the same functionality which takes flags and input as plain
strings, intended for interactive usage in ghci.
