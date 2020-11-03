## elabzoo-holes

Minimal implementation of an elaborator with holes and pattern unification. Extensive
comments are included in the implementation.

Further reading, roughly in preferred order:

- Ulf Norell's PhD thesis, chapter 3,
  http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf This is the closest to the
  current implementation, also provides a concise and digestible introduction to
  unification, implicit insertion and constraint postponing. A good reference to
  the implementation in Agda, but covers only a small part of the current far
  more sophisticated Agda. Implicit insertion, however, has a more elegant
  implementation in the `04-implicit-args` project here.

- http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf Very good resource
  for some of the advanced tricks in Agda (which are not explained in the
  previous reference), but it's a bit heavier read, and by itself not very
  helpful with respect to actual implementation.
- https://www.irif.fr/~sozeau/research/publications/drafts/unification-jfp.pdf
  This Coq unifier guide goes into lots of delicious dirty details. Very good
  read, although I disagree with a number of design decisions there.
