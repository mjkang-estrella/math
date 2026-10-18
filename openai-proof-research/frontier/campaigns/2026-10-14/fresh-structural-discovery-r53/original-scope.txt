# Frozen target BUC: a connected bipartite uncommon graph

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party materials retain their original rights privately.

There exist a finite connected simple bipartite graph F with at least one
edge, a finite nonempty probability space (Omega,mu), and a symmetric
function W:Omega x Omega -> [0,1] such that, writing m=|E(F)|,

  t(F,W) + t(F,1-W) < 2^(1-m).

Here t(F,K) is the expectation of product_{uv in E(F)} K(X_u,X_v)
for independent mu-distributed X_v; EVERY homomorphism is counted.
No restriction on F, its order, degree, girth, balance or relation to the
source graph, on the number or masses of atoms, or on W is imposed.
Equivalently there is a connected bipartite pattern whose asymptotic
two-color Ramsey multiplicity is strictly below the random-color bound.
A refutation must prove the displayed lower bound for EVERY such F,W.

The source family is 161 at openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its thm:main provides a fixed
35-vertex 66-edge connected bipartite H and ONE-SIDED Sidorenko deficit.
Its prop:negative-kernel supplies a finite symmetric [0,1] witness;
cor:amplification and cor:forcing do NOT assert this two-color target.

Operation screened before sustained work: construct a bounded complementary
pair carrying the negative global incidence correlation in BOTH colors,
while bounding all proper even-edge correlations. The concrete mechanism
under investigation is a product/type lift with a complement-swapping
involution, using the even 66-edge source correlation and its explicit
activation supports; rooted attachments and coordinate switches are allowed.
The full target is NOT restricted to this mechanism or to source H.

Primary screening: Kral--Noel--Norin--Volec--Wei, arXiv:2006.09422v3,
Theorem2 and its complete Section4 proof, establishes only k-uncommonness
for SOME finite k from a Sidorenko deficit, by averaging all type
permutations into a partition of unity. Its operation increases colors;
it does not supply k=2. Its Proposition7 gives the edge-subset expansion,
and Theorem8 records local positivity for even-girth patterns. Thus small
balanced perturbations cannot simply transfer the source deficit.
The source's crossed rectangular product symmetrizes orientation, not
complement colors; its final scaling can have very small mean.
This freeze is a research assertion, not a success or novelty claim.
No independent PASS, nomination, count, manuscript or Lean claim is made.
