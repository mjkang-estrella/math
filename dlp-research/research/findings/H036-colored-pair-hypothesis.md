# H036 coefficient-colored paired sums

Status: PAPER candidate, normalized-equation audit completed; whole-work gain
unproved. Independent review validated the algebra with the conditions below.
Origin: GPT6Sol independent search-geometry card1, retained raw. Root supplied
the following concrete falsifier and deterministic-color attempt. No experiment,
source change or accepted algorithmic improvement. No novelty claim.

Prepare independent labels P_i=a_iG+b_iQ and cache cP_j for a small public
coefficient set c in{2,...,K+1}. For selected directed edges i<j emit exact
abscissae of P_i±c_ij P_j with known descriptors. Recovered equalities yield
linear scalar equations; nulls, verification, fallback and all memory are paid.
The paired generation kernel is shared with H019/H034. A source of potential
gain is fewer repeated four-source equations without the sparse C4-free graph.

Root's conjectural local test: for sorted vertices i<j<k<l, normalize each
four-support relation by its coefficient at i. If all colors exclude±1, the
pairing(ij)(kl) cannot coincide with either alternative pairing. The pairings
(ik)(jl) and(il)(jk) can coincide only when c_ik=c_jk and c_il=c_jl, modulo
sign/projective qualifications still under review. IID K colors would suggest
a1/K² repeated-form fraction, but sampling/storing every edge color is leading
work and cannot be omitted.

A concrete deterministic attempt uses a small prime K, row parameters

    a_i=floor(i/K) modK, b_i=i modK, t_j=j modK,
    c_ij=2+((a_i*t_j+b_i) modK).

Root conjectures O(n⁴/K²+n³) bad rectangles, requiring uniform prefix control
and all scalar-proportionality cases. Incremental row enumeration can avoid a
fresh wide multiplication per edge, but its small-field/index work is still
charged. Cache construction needs nK full points by successive additions;
the cache is visible preprocessing and peak storage, not advice.

Even under the optimistic count, n~q^(1/4) gives setup/cache scale nK and a
stopped-key penalty sqrt(q)/K². Balancing these suggests K~q^(1/12), overhead
q^(1/3), worse than the existing restricted thickened-graph q^(3/10) surrogate.
This is a heuristic cost screen, not a lower bound or validated moment theorem.
Polylogarithmic K could approach the ideal leading birthday constant with
smaller seed exponent but slow finite convergence. Leading color enumeration,
descriptors, detector and baseline costs may erase any benefit.

Cheap decisive next step: independently classify normalized four-support
vectors and count duplicates before any curve execution. Native Astra
/root/h007_additive_relations is assigned that exact read-only task. A favorable
count would still need stopped-law, null-recovery and complete-cost review.

Other independent cards remain unscreened: cached-pair three-source hyperedges
and correlated short-jump seed factories. Both need explicit relation-rank and
cache/setup counts; neither inherits H034's independent-source law for free.

## Completed independent normalized-vector audit

Native Astra accepted the mechanism under2(K+1)<q. After normalizing the
coefficient at the smallest vertex to1, no additional projective factor remains.
The first pairing is disjoint from the other two. Those two share all eight
forms exactly when the two displayed color equalities hold, and none otherwise.
For a full n-vertex prefix the exact four-support event count is therefore

    N4=24*choose(n,4)-8R.

For independent uniform colors E[N4]=24*choose(n,4)*(1-1/(3K²)). This corrects
any reading of1/K² as the normalized count deficit; it is only the bad-rectangle
probability. For the deterministic affine array, distinct row functions agree
on at most one column residue, present at mostceil(n/K) times. Identical row
functions repeat everyK² indices. This proves R=O(n⁴/K²+n³).

Use increasing newest vertex j, then all i<j, as the explicit edge order. A
partial final row adds O(n) keys and changes the count by O(n³). For t emitted
keys this gives N4=t²+O(t²/K²+t^(3/2)). Arbitrary edge order is not covered.
Shared-vertex forms number O(n³) and still require a stopped-law proof.

Additional obligations from the review: dispatch x(P_i)=x(c_ij*P_j), including
identity/tangent/vertical cases; original seed uniqueness is insufficient.
Scaled helper points are not free additional searched keys. Labels must be
(a_i±c_ij*a_j,b_i±c_ij*b_j). Geometric-first selection, under ideal independent
seed labels, retains the usual conditional1/q null-coefficient statement.
No resulting complete-cost theorem has been accepted.

The eager nK helper table needs nK incremental additions. Root notes that this
newest-vertex order can instead retain only the current vertex's K helpers,
releasing them after its row; stored source roots plus K helpers then suffice
for point inputs. This reduces helper peak, not the total nK generation work,
and does not remove the archive or descriptor storage. The q^(1/3) balance is
therefore a work screen, not a universal memory lower bound. No source change
or computation was used to infer this simple streaming alternative.

Disposition: retain a valid distinct relation-generation construction, park its
current work claim because the charged balance does not improve the existing
q^(3/10) surrogate. A cheaper scaled-helper construction or a different color
tradeoff could reopen it; do not expand general infrastructure around this one.
