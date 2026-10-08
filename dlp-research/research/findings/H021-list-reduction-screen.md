# H021 signed-list reduction and four-list enumeration gate

2026-10-08. Factory Opus initial card in H020-public-signal-factory-raw.md;
independent native Astra /root/h007_additive_relations review COMPLETED.
Root checked the reduction and second-moment calculation below. Paper results,
not Lean proofs, numerical measurements or an improved ECDLP solver.
Verified improvement NONE. Review brief in H021-public-signal-reviews.md.

## Exact supplied-curve reduction

Fix a supplied certified E/F_p with full prime order q and generator G.
For three independent uniform nonzero residue lists, a -> [a]G exactly
preserves their product distribution as point lists. A signed point-relation
detector therefore solves the corresponding signed modular3SUM problem.
Convert inputs using O(n log q) group operations, charge curve setup,
certification, preprocessing, input storage and final witness verification.
When p is comparable to q, conversion is n*polylog(q) bit work. Supplied
logs must be those of the actual converted inputs. Extra promises involving
target-dependent labels do not automatically follow from this reduction.

Signedness itself can be removed at constant success loss. Independently
multiply each original modular input by a hidden fair sign before passing it
to the signed detector. Uniform residues make those signs independent of the
transformed instance and output witness. The three returned witness signs
agree with the hidden signs up to common negation with probability1/4, which
gives an unsigned witness on the original inputs. Conditioning out zero
residues loses at most3n/q probability. List partitioning and constant-factor
list sizes require their stated success losses; do not omit them silently.

The reviewer read Dinur–Keller–Klein, [full primary paper](https://arxiv.org/pdf/2111.00486),
Definitions1.1/4.2, Conjecture1.2 and Lemmas4.4/4.5. Unlike the initial
abstract-only report, the paper explicitly defines modular k-MSUM and relates
it to the integer problem. Lemma4.5 has success loss depending on N/M and k;
with k fixed and modulus M comparable to the integer range N this is constant.
The sparse conjecture asks constant success and near-quadratic work for k=3.
These statements do not construct an EC of a desired prime order.

Consequently a sub-n^(3/2) random-list detector has a conditional complexity
consequence if a suitable curve family is uniformly available within budget,
or if the hardness assumption explicitly allows the supplied curve advice.
Do not state unqualified SP3 hardness, a fixed-curve asymptotic theorem, or a
coordinate-aware lower bound. Structured, adaptive, preprocessed and
multi-target detectors require separate reductions. No experiment follows.

## Four-list modular construction: dependence accounted for

Four independent lists A,B,C,D each contain n uniform residues modulo q.
Choose a symmetric centered interval S with odd size L<q. Count indexed
witnesses with A_i+B_j in S and A_i+B_j+C_k+D_l=0. Then

    mu = E[Z] = n^4 L/q^2,
    Var(Z) <= mu + 2 n^6 L/q^3.

Proof: distinct quadruples sharing neither complete left nor complete right
pair have independent indicators, including when one index in a pair overlaps.
If one complete pair is shared, joint probability is L/q^3. At most n^6
ordered comparisons share each complete pair; the identical-quadruple term
is at most mu. For n proportional to q^(1/3), L proportional to q^(2/3),
mu is bounded away from zero and infinity, and the extra variance is
O(q^(-1/3)). E[Z]^2/E[Z^2] therefore supplies constant success.

Each intermediate pair-list length X has mean n^2L/q proportional to n
and variance at most that mean, by pairwise independence of pair-sum tests.
Capping output at Cn for a sufficiently large fixed C loses O(1/n) success.
Sort B and range-report S-a (at most two cyclic intervals) for each a;
repeat for C,D, then sort/match opposite sums with their indices retained.
Time is softO(n), storage O(n) records. Caps bound unfavorable outputs,
and correctness does not assume an instance has a witness. All records have
O(log q) bits. This is a Wagner-style modular construction, not new ECDLP art.

## Concrete missing EC primitive

The counting argument uses only the group and a fixed subset of size L,
so it transfers to a fixed EC subset S (use -S for the second pair if needed).
The range-reporting implementation does NOT transfer automatically. Need a
compact public S of size about q^(2/3) and an index on an n-point list that
reports all B with P+B in S in polylog(q) time plus output, including paid
construction, exact signs, records, memory and worst-output handling.
Uniform points alpha_i G+Q as the first list give target coefficient1;
known-log other lists then allow direct recovery and scalar verification.

This is a specific route to softO(q^(1/3)) only CONDITIONAL on that unbuilt
primitive. No coordinate key or paid enumeration algorithm was supplied.
Counting runs in one key order can reject only that particular union-of-ranges
representation. Degree or a failed key order does not exclude every index.
H001's accepted disposition already corrected the raw quotient-homomorphism
objection; preserve that history rather than claiming a new correction.

Next conclusion-changing work is an actual EC index with a favorable complete
cost ledger. Until then there is no implementation to benchmark and no reason
to build generic formal infrastructure. No full-size hardness estimate changes.
