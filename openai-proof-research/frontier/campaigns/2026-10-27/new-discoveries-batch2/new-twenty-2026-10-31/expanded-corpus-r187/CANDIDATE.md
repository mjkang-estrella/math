# 340386: mathematically valid refutation, excluded from new-credit recommendation

Source: Peter Beelen and Sudhir R. Ghorpade, arXiv:1809.04690v1,
Conjecture 2.5(3), equations (3) and (4), and Fact 2.1. The published
Discrete Mathematics 343 (2020), 111965 version retains Conjecture 2.5
in the indexed author-copy excerpt. Direct author-copy download timed out;
full version-of-record comparison is not claimed.

For q = 2, ell = m = 4 and t = 2, the four actual projective-code weights are
3200, 3776, 3808, 3760. Thus w_4 is below both w_2 and w_3, contrary
to clause (3). Over F_2 each nonzero matrix already represents its unique
projective point. The source's Fact 2.1 identifies weight w_r with the
number of rank-at-most-two matrices with nonzero r-th partial trace.

Independent enumeration: scripts/weights-independent.py visits all 65536
binary 4 by 4 matrices. XOR row elimination gives the rank histogram
1, 225, 7350, 37800, 20160. Direct parity evaluation of each partial trace
on ranks at most two gives the four weights above. This computation is
independent of the source's weight formula, but is diagnostic, not a Lean proof.

An ordinary proof follows immediately from the source's established formula.
Let K_s(r) be the inner alternating Gaussian-binomial sum in equation (3).
The rank-one and rank-two counts are 225 and 7350. For r = 1, 2, 3, 4,
the sums K_1(r) + K_2(r) are 1175, 23, -41, 55, respectively.
Equation (4) therefore gives w_r = (7575 - K_1(r) - K_2(r))/2,
which yields the stated weights. This is a complete ordinary refutation,
conditional only on the published formula.

The phenomenon persists, rather than being an isolated order-four anomaly.
For q = 2, ell = m = L >= 4, t = 2, direct simplification of the same
formula gives

    w_L - w_(L-2) = 2^(L-1) (6 - 2^(L-1)) < 0,
    w_(L-1) - w_(L-2) = 2^(L+1) > 0.

Indeed, after subtracting the common K-sum at r = L, the K-sum at
r = L-2 is 2^L (6 - 2^(L-1)), and that at r = L-1 is
2^L (2 - 2^(L-1)). Multiplication by -1/2 gives the identities.
Thus clause (3) fails for every square binary determinantal code in this
family. The sweep found 352 failures in 19894 parameter tuples; all were
binary square cases. This is bounded evidence, not a classification proof.

Credit verdict: EXCLUDE / do not advance to Lean. The binding brief gives
zero credit to proofs whose new part is a few lines on the source's claims.
This refutation and even its infinite extension are direct evaluations of
equations (3) and (4), with no new counting theorem. Its mathematical
correctness does not overcome that explicit credit rule. Root retains final
adjudication. No Lean endpoint, acceptance, priority, or complete registry
clearance is claimed. No artificial Lean packet is supplied for an excluded
route.

Prior-art evidence and limits: sources/weights-prior.json,
sources/literature-0.json, sources/citing-0.json, outputs/registry-screen.json.
No exact previous counterexample was located in those bounded searches.
Lean Pool projects/candidates were screened at its recorded HEAD. GitHub
repository searches were capped at eight; the determinantal query was broad
and did not combine every author and arXiv identifier. Registry path screening
cannot certify absence of implication by a differently named theorem.
