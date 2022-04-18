# Experiments with delimited continuations

- [A Functional Abstraction of Typed Trails by Kenichi Asai, Youyou Cong, Chiaki Isio](https://popl21.sigplan.org/details/pepm-2021-papers/4/A-Functional-Abstraction-of-Typed-Trails)
- [A Functional Abstraction of Typed Contexts by Olivier Danvy, Andrzej Filinski](http://www.mpi-sws.org/~skilpat/plerg/papers/danvy-filinski-89-2up.pdf)
- [A static simulation of dynamic delimited control by Chung-chieh Shan](http://homes.sice.indiana.edu/ccshan/recur/recur-hosc-final.pdf)
- [Shift to control by Chung-chieh Shan](http://homes.sice.indiana.edu/ccshan/recur/recur.pdf)
- [How to remove a dynamic prompt: static and dynamic delimited continuation operators are equally expressible by Oleg Kiselyov](https://legacy.cs.indiana.edu/ftp/techreports/TR611.pdf)

[this explanation by Sebastian Fischer](https://gist.github.com/sebfisch/2235780) which relates them to exceptions or [this explanation by Andy Wingo](https://wingolog.org/archives/2010/02/26/guile-and-delimited-continuations) which shows the implementation details.
[intro to the indexed continuation monad](https://gist.github.com/pthariensflame/5716594)

In this paper they present a type system for `prompt`/`control` based on the CPS conversion described in [Shift to control by Chung-chieh Shan](http://homes.sice.indiana.edu/ccshan/recur/recur.pdf). This CPS conversion adds along side the normal `k` a second argument, named either `t` or `mc` and referred to as a trail. This argument is only touched in the conversions of `prompt` and `control`. This paper extends a type system given in [A Functional Abstraction of Typed Contexts by Olivier Danvy, Andrzej Filinski](http://www.mpi-sws.org/~skilpat/plerg/papers/danvy-filinski-89-2up.pdf) to account for this additional argument.

That was [my first experiment](https://github.com/CoderPuppy/dcont/blob/3f09b11a4b5edfc42fc37abaa0988f22ac801dcd/Types1.hs): implementing this CPS conversion and type system in Haskell. It converts the constraints used in the paper into type classes. This led to an interesting question: are the types generally inferable? These are multi-parameter type classes without functional dependencies and with an almost ambiguous type variable, so it's not obvious.

[My second experiment](https://github.com/CoderPuppy/dcont/blob/cad3a6d0ee281d82d5f4da4c52dbfb51a6e4b863/Types2.hs) came from a question I had just from the paper itself: how does it relate to the [earlier](http://www.mpi-sws.org/~skilpat/plerg/papers/danvy-filinski-89-2up.pdf "A Functional Abstraction of Typed Contexts by Olivier Danvy, Andrzej Filinski") type system? In this experiment I converted the definitions of `prompt` and `control` from the later type system to the earlier one. TODO

For that experiment I looked to [Shift to control by Chung-chieh Shan](http://homes.sice.indiana.edu/ccshan/recur/recur.pdf) to see how to implement `prompt` and `control` in terms of `shift` and `reset`. Unfortunately doing so would have changed the type system somewhat, so I cheated by using the fact that as long as all `shift`s are within `reset`s the answer types can be anything. For [my third experiment](https://github.com/CoderPuppy/dcont/blob/cad3a6d0ee281d82d5f4da4c52dbfb51a6e4b863/Types3.hs) I fixed that by keeping around the answer type irrelevance of captured continuations. This allows it to be easily extracted to a language only supporting `shift` and `reset` without also requiring `prompt` and `control` as primitives.

TODO I've had a goal from the start of these experiments, typing the conversions in [How to remove a dynamic prompt: static and dynamic delimited continuation operators are equally expressible by Oleg Kiselyov](https://legacy.cs.indiana.edu/ftp/techreports/TR611.pdf). Unlike [Shan's approach](http://homes.sice.indiana.edu/ccshan/recur/recur.pdf "Shift to control by Chung-chieh Shan") it takes a much more local and orthogonal approach to implementing `prompt`/`control`, `shift0`/`reset0` and `prompt0`/`control0` in terms of `shift` and `reset`. In [my fourth experiment](https://github.com/CoderPuppy/dcont/blob/cad3a6d0ee281d82d5f4da4c52dbfb51a6e4b863/Types4.hs) I came up with a type system based on these conversions. It splits Kiselyov's `H` type into two, one for `H` and one for `HV`. It then encodes his `h` and `h'` functions as a type class, thus lifting the match over `H` to the type level. When compared to the [type system](https://popl21.sigplan.org/details/pepm-2021-papers/4/A-Functional-Abstraction-of-Typed-Trails "A Functional Abstraction of Typed Trails by Kenichi Asai, Youyou Cong, Chiaki Isio") which started this, it is somewhat messier and possibly less general. It does however support all the dynamic control operators (`prompt`/`control`, `shift0`/`reset0` and `prompt0`/`control0`).

TODO Types5.hs: hide types in H by using functions

TODO Types6.hs: combine H and HV

TODO Types7.hs: different typing

dynamic-wind
multiple prompts
correspondance
inferability
