## elabzoo-implicit-args

This package implements named implicit arguments following Agda convention and
behavior, with first-class implicit dependent function types.

Additionally, we have a way to stop meta insertion at any point in an application spine using `!` , 
so e.g. given `id : {A} -> A -> A`, we elaborate `id!` simply
to `id`, with no hole inserted for the `A` implicit argument.
