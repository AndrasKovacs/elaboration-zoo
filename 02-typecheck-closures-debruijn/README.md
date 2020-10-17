
#### elabzoo-typecheck-closures-debruijn

Minimal dependent typechecking. Based on Coquand's algorithm:

https://www.sciencedirect.com/science/article/pii/0167642395000216

See also David Christiansen's tutorial:

http://davidchristiansen.dk/tutorials/nbe/

This implementation uses first-order closures and de Bruijn indices/levels. This
is the basis of all further projects. Names are much less efficient and a lot
harder to reason about than indices/levels, so they are only used pedagocically
in the simpler projects.
