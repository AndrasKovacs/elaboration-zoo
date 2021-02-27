
#### elabzoo-typecheck-closures-debruijn

Minimal dependent typechecking. There's a video explanation:

https://www.youtube.com/watch?v=_K5Yt-cmKcY

See also David Christiansen's tutorial:

http://davidchristiansen.dk/tutorials/nbe/

The original version is Coquand's algorithm:

https://www.sciencedirect.com/science/article/pii/0167642395000216

This implementation uses first-order closures and de Bruijn indices/levels. This
is the basis of all further projects. Names are much less efficient and a lot
harder to reason about than indices/levels, so they are only used pedagocically
in the simpler projects.
