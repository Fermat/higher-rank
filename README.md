# higher-rank

A prototype type checker for higher-rank, impredicative and second-order types.

* Install

  cabal install or stack build

* Type check a file

  higher-rank-exe examples/bird.hr

* Program syntax

  basically haskell syntax, but much more limited, please see files in examples/. 

* Behavior

  the output will be either error message, or the annotated version of the input programs. 

* Output syntax

  \\\\ for type abstraction, @T for type application, machine generated variables will be postfixed with \#.

* More information

  please see the accompany paper. 