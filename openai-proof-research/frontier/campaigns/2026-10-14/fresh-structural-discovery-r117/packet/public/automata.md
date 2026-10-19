# Relation liveness and randomized restart: exclusion calculation

The pinned deterministic source129 has an (h+3)-state one-way nondeterministic recognizer of one-way liveness over the alphabet of all binary relations on [h]. Every s-state deterministic two-way recognizer obeys `4(s+2)^2 >= 2^floor((h-2)/31)`. Its `machines.tex`, `thm:machine-diagrams`, uses a deterministic functional configuration graph, tree components and contour matchings; nondeterministic or stochastic branching is not the same contract. `separation.tex`, `prop:small-nfa` and `lem:syntactic-quotient`, supplies the relation-product interface.

The separate pinned complementation companion, `main:theorem`, gives an exponential lower bound for two-way **nondeterministic** recognition of product emptiness. Neither statement bounds probabilistic recognition with a time-dependent acceptance probability. Both count states rather than alphabet/transition-table size.

## Direct calculation

Fix h>=2 and a word w=R_1...R_L. Let N(w) be the number of sequences (p_0,...,p_L) in [h]^(L+1) whose consecutive pairs lie in the corresponding relations, and set Q=h^(L+1). Then w is live exactly when N(w)>0. The empty word has N=h and is live.

Build the following two-way probabilistic finite automaton using rational transition probabilities and O(h) states. At each round start choose between two branches with probability1/2 each.

* In the acceptance branch choose p_0 uniformly from[h]. On each relation symbol choose the next state uniformly from[h]; if that edge is missing, enter a failure flag and scan to the right endmarker. A completely successful path accepts at that marker. The branch's one-round acceptance probability is N/(2Q).
* In the rejection branch survive an initial coin of probability1/(2h), then a coin of probability1/h on each relation symbol. A survivor rejects at the right endmarker. Failed trials scan to the right marker. The one-round rejection probability is 1/(4Q).

Every other outcome enters a deterministic rewind mode, moves the head left to the actual left endmarker, and starts a fresh round. No teleport or input-length counter is a machine primitive. The states store only a path vertex, a branch/survival flag, or a rewind mode. Since the alphabet is finite for each h, its large transition table can hardwire membership in the scanned relation. These are rational-probability automata; no fixed coin-denominator or succinct transition-table claim is made.

A round has length O(L+1), and its halting probability is at least1/(4Q), so it halts almost surely with expected time O((L+1)h^(L+1)). Summing the geometric series gives eventual acceptance probability

    [N/(2Q)]/[N/(2Q)+1/(4Q)] = 2N/(2N+1).

For N=0 it rejects with certainty; for N>=1 it accepts with probability at least2/3. Interchanging the halting labels gives the complementary language with the same bounded error, state count and time bound.

This normalization is exactly the classical restart operation in [Yakaryılmaz–Say, *Proving the power of postselection*, arXiv:1111.3125v1](https://arxiv.org/pdf/1111.3125v1), §3 Lemma1. The primary uses abstract restart; the explicit rewind above implements it in the present ordinary two-way model. Its linked correction PDF timed out, so no claim is made to having checked the correction or all later language-class claims. The geometric-series identity used here is independently displayed and does not depend on those unread claims.

The construction refutes only an attempted extension of this particular source-family exponential state lower bound to unrestricted-time bounded-error two-way probabilistic machines. It is not a new structural nomination. Exponential expected time is essential in this argument; no polynomial-time statement follows.

## Existing binary compilation

Actual r31 `screen-129.md` already gives a two-bank rotation/copy/delete binary encoder with at most14h+2 NFA states and a constant-overhead two-way macro pullback. Its proof hardwires finite block exit relations, including arbitrary reentries and nonaccepting internal loops. Actual r38 `technical129.md` also reconstructs binary encoding. The r31 body was read late during final historical reconciliation, before any freeze (none occurred). New alphabet constants or replacing the exponential source rate in that known compiler do not supply a fresh mechanism. The present restart calculation does not alter these deterministic/nondeterministic lower bounds.
