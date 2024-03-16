Random proofs in Lean 4.

## tao_analysis_i

This is my attempt at formalizing Terence Tao's Analysis I.
I gave up in the middle of chapter 4 because setoids were not fun to work with.

This project can compile under Lean 4.7.0-rc1.

## rayleigh_beatty

This is my attempt at formalizing [Wikipedia's proof of Rayleigh's theorem](https://en.wikipedia.org/wiki/Beatty_sequence#Second_proof). My attempt was successful.

I submitted a [pull request](https://github.com/leanprover-community/mathlib4/pull/7027) to mathlib4 and it was merged after some fairly heavy modifications. The mathlib4 docs are available [here](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Rayleigh.html).

This project can compile under Lean 4.7.0-rc1.

## SquarePyramid

This is my attempt at formalizing Anglin's proof of the [cannonball problem](https://en.wikipedia.org/wiki/Cannonball_problem). My attempt was successful and I created a summary PDF ([link](SquarePyramid/cannonball_summary.pdf)).

This project can compile under Lean 4.7.0-rc1.

## BusyLean

This is my attempt at formalizing a "Finite automata reduction" certificate checker (see Chapter 6 of [this PDF](https://github.com/bbchallenge/bbchallenge-proofs/blob/main/deciders/correctness-deciders.pdf)). Here's a quick intro:

* The goal of [bbchallenge](https://bbchallenge.org/story) is to prove that the 5th busy beaver number is 47176870.
* As part of bbchallenge, many people have written *deciders*. A decider takes as input a Turing machine and outputs either *halt*, *non-halt*, or *undecided*. Some deciders also output an easily-checkable certificate.
* One decider is named "Finite automata reduction" (FAR). This is a powerful decider that leaves ~10 Turing machines undecided. This decider also outputs easily-checkable certificates.
  * Side note: Most of the ~10 undecided machines were [formally proven in Coq](https://github.com/meithecatte/busycoq/tree/master) to not halt.
* There are FAR certificate checkers, but they have not been formally verified.

Goals:

* Prove Theorem 6.4.
* Find a way to get Lean 4 to accept a FAR certificate. i.e. given a non-halting Turing machine and its FAR certificate, prove that the Turing machine does not halt.

So far, Theorem 6.4 has not been proven yet in Lean 4.
