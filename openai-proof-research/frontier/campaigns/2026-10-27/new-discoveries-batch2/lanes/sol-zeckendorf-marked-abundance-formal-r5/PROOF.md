# Finite MGF route and exact remaining formal obligation

This is an ordinary proof explanation; SUMMARY identifies its unclosed Lean step.
Let N be natural, n>=1, and N<F_(n+1). The requested F_n<=N may be added without
changing any argument. Let Omega=completeDomain N with weights P N, J=floor(N/6),
p=(2n)^(-3), and Y_j count successful triples among block indices <j.

The certified prefix cylinder sum is the reciprocal product of legal-type counts.
This follows by the proved bijection with normalized terminal continuations from
the endpoint board, with weights factored by reciprocal_append. Thus conditioning
on an executable prefix has the literal branch law, rather than an assumed one.
Every complete word has length >=3J. At a prefix of length 3j, j<J, at least
N-6j>=6 ones remain. Each of the three chosen moves is legal, and their reciprocal
branch factors are >=1/(2n); their cylinder ratio q_u is >=p. This establishes
conditional success for every positive prefix cylinder of the actual finite law.

For each such cylinder, Y_j is fixed, say y. Its one-block split gives exactly

 sum_(w in cylinder u) P(w) * 2^(-Y_(j+1)(w))
   = cylinderMass(u) * 2^(-y) * ((1-q_u)+q_u/2)
   <= cylinderMass(u) * 2^(-y) * (1-p/2).

The length-3j prefix cylinders are a disjoint exhaustive partition because all
words have at least 3J moves. Summing and inducting gives M_J<= (1-p/2)^J,
starting with M_0=sum P=1. This finite partition summation and moment induction
are the remaining FORMAL obligation, not certified endpoints in this packet.
There is no independence assertion: q_u may depend on the entire prefix.

The certified injection sends a successful block j to compressed-prefix length
before its final C2. Compression before this move preserves its board; two C1s
created at least two twos. Appending C2 does not create a crossing S2,C1 pair.
A preceding S2 can consume only the first of the two C1s; the same prefix-index
formula still applies. A later disjoint successful block has a strictly greater
index, by compression-prefix length monotonicity and the intervening C2.
Hence the marked count m is >=Y_J, as a proved finite cardinal inequality.
On m<t, Y_J<t and 1<=2^t*2^(-Y_J). Multiply by nonnegative actual P(w), sum, and
use the MGF inequality to obtain the requested 2^t*(1-p/2)^J bound.
For t=0 the bad event is empty; for N<6, J=0 and the bound is trivial. N=0 has
only the empty word, so bad mass is 1 for t>0 and 0 for t=0. No n=0 claim is made.

Provenance: root-zeckendorf-product-disposition-r5/STATUS.md explicitly supplied
the rational finite-MGF route. r284 PROOF.md supplies the earlier adaptive-trial
ordinary abundance argument and warns against interpreting raw trials as
independent. Primary arXiv:2210.11038v1, Lemma4.4 proof p19, contains the triple
idea and an independence sentence; this packet does not import that sentence.
The simpler S2,C1 compression partition is the inherited Cells object, not the
source's richer all-k partition. No concentration or final mixing is claimed.
