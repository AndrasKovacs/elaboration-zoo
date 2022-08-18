
#### mltt-lock

MLTT-lock implementation: https://dl.acm.org/doi/10.1145/3341711

Only has Pi and type-in-type.

There's also a closed evaluator which interprets the modality as runtime code
generation.

- When the closed evaluator hits a splice ("unbox"), it runs the code generator
  (a term with type `□ A`) then evaluates the generated term.
- When it hits a quote ("box"), it evaluates all next-stage splices in the quoted term and
  returns the resulting term.

It seems that we need some kind of contextual modality for codegen purposes,
mainly because using `□` and functions to represent open terms yields a very large
number of "administrative" redexes.

There's Moebius: https://arxiv.org/pdf/2111.08099.pdf But I would like to also
see a nice version of contextual types in Fitch style, because as far as I see
the negative eliminator if just far more convenient than the positive one.
