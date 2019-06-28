# elaboration-zoo

Work in progress. Each numbered directory contains a
[stack](https://docs.haskellstack.org/en/stable/README/) package. In each
directory, the `stack build` command builds the executable, and `stack ghci` can
be used to load the package.

Generally, every package has a `main` function which takes some command line
flags and reads input from stdin, intended for command line usage, and a `main'`
function with the same functionality which takes flags and input as plain
strings, intended for interactive usage in ghci.
