## BusyLean

This is my attempt at formalizing a "Finite automata reduction" certificate checker (see Chapter 6 of [this PDF](https://github.com/bbchallenge/bbchallenge-proofs/blob/build-latex-pdf/deciders/correctness-deciders.pdf)). Here's a quick intro:

* The goal of [bbchallenge](https://bbchallenge.org/story) is to prove that the 5th busy beaver number is 47176870.
* As part of bbchallenge, many people have written *deciders*. A decider takes as input a Turing machine and outputs either *halt*, *non-halt*, or *undecided*. Some deciders also output an easily-checkable certificate.
* One decider is named "Finite automata reduction" (FAR). This is a powerful decider that leaves ~10 Turing machines undecided. This decider also outputs easily-checkable certificates.
  * Side note 1: A lot of FAR certificates were created in an ad hoc way. This matters for certificate creators, but not for certificate checkers.
  * Side note 2: Most of the ~10 undecided machines were [formally proven in Coq](https://github.com/meithecatte/busycoq/tree/master) to not halt.
* There are FAR certificate checkers, but they have not been formally verified.

Goals:

* Prove Theorem 6.4.
* Find a way to get Lean 4 to accept a FAR certificate. i.e. given a non-halting Turing machine and its FAR certificate, prove that the Turing machine does not halt.

So far, Theorem 6.4 has not been proven yet in Lean 4.
