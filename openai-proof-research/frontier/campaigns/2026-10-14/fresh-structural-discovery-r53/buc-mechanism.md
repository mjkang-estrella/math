# BUC continuation: endpoint signs and the fixed-pattern local barrier

Author-side support, not a candidate theorem or independent review. The full
r17 target is copied byte-for-byte in original-scope.txt. It remains unresolved.
Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.

## 1. Exact endpoint-sign expansion

Let (Omega,mu) be any finite probability space and U a symmetric [-1,1]-valued
kernel. On Omega times a fair independent sign, define

 V((x,s),(y,t)) = (s+t)U(x,y)/2,    W=(1+V)/2.

Flipping every sign preserves measure and sends V to -V. Consequently W and
1-W have the same density for every graph. For a subset A of the edges of a
finite simple graph F, let v_+(A) count nonisolated vertices and c(A) count
nontrivial connected components. The empty subset has both counts zero. Then

 t(F[A],V) = 2^(c(A)-v_+(A)) t(F[A],U)

if every nontrivial component of A has an even number of edges; otherwise it
is zero. Here F[A] retains the full vertex set; isolated vertices integrate out.

Proof: an edge factor vanishes when its endpoint signs differ. Thus signs
must be constant on each nontrivial component. A component with v vertices
and e edges contributes 2^(-v)(1+(-1)^e), independently of the Omega labels.
Multiplication proves the formula. No injectivity, regularity or zero-mean
assumption is used.

Expanding the product therefore gives the exact identity

 2^(e(F)-1) [t(F,W)+t(F,1-W)]
 = 1 + sum_{nonempty A, each component edge-even}
          2^(c(A)-v_+(A)) t(F[A],U).

For k independent sign coordinates multiplying the same U, each coefficient
is instead 2^(k(c(A)-v_+(A))). The full source graph H (35 vertices,66 edges)
survives with coefficient 2^(-34k). A two-edge path survives with coefficient
2^(-2k). These comparisons alone do not prove an obstruction: the path
quantity is the squared L2 norm of the row mean and can vanish.

The parent independently derived the same identity in buc-parent-r1. Neither
independent derivation is an independent campaign gate. The parent finite
check is not needed for this proof and was not copied as our own diagnostic.

## 2. A negative full term does not suffice

Consider the four-edge tree with edges 01,02,03,34. On two equal atoms take

 U = [[-1,3/4],[3/4,-1/4]].

Its row means are -1/8 and 1/4. Direct exact evaluation gives
 t(F,U)=-5/4096,    t(P3,U)=5/128.
There are four two-edge paths in F. These and the full edge set are exactly
the nonempty edge subsets whose every component has even edge count.
Thus the normalized two-color sum for the endpoint construction is

 1 + 4*(1/4)*(5/128) + (1/16)*(-5/4096)
 = 1 + 5/128 - 5/65536 > 1.

This demonstrates the logical error in keeping only a surviving negative
full term. It is not a counterexample to BUC or a universal obstruction to
endpoint-sign constructions. checks/exact_example.py evaluates the densities
by exhaustive finite sums using rational arithmetic; it is supporting evidence
for this explicit calculation, not a proof of the unresolved target.

## 3. Fixed-pattern normalization and tensor barrier

The following is a direct application of an existing local Sidorenko theorem,
not a substantial new theorem. Lovasz, arXiv:1004.3026v1, Theorem 3.1, states:
for a simple bipartite F with m edges, a mean-one kernel Z with 0<=Z<=2 and
||Z-1||_cut <= 2^(-8m) satisfies t(F,Z)>=1. The actual v1 statement and its
complete proof were read. This packet uses that version, without conflating
its numbering or constant with the published version.

Let K be any finite symmetric nonnegative mean-one kernel. Choose
M >= max(1,||K-1||_infinity), and put U=(K-1)/M. Then
||U||_infinity<=1 and ||U||_1<=2/M. For its endpoint lift V,

 integral V=0,       ||V||_1=(1/2)||U||_1<=1/M.

(The sign expectation of the absolute endpoint factor is 1/2.) Therefore
Z=1+V lies in [0,2], has mean one, and ||Z-1||_cut<=1/M. If
M>=2^(8m), the cited theorem gives t(F,1+V)>=1. Sign symmetry gives the same
for 1-V and hence t(F,W)+t(F,1-W)>=2^(1-m).

There are two different repetition operations:
* Multiplying k independent endpoint-sign factors against the SAME U gives
  L1 norm 2^(-k)||U||_1 <= 2^(1-k)/M. Once this is at most 2^(-8m), the same
  local theorem applies. The exact coefficients are those in Section1. Independently of normalization,
  ||U||_1<=1 also gives ||V_k||_1<=2^(-k), so k>=8m suffices for
  ANY bounded U. This optional sharpening was supplied by the parent.
* Taking a tensor product V^{tensor r} on independent copies of the ENTIRE
  enlarged probability space gives L1 norm ||V||_1^r<=M^(-r), sup norm<=1,
  and mean zero. Flipping the sign coordinate in one factor negates the
  whole kernel. When M^r>=2^(8m), it too cannot witness uncommonness of F.

Arbitrary finite atom masses are covered: represent each atom by an interval
of its mass and use a step kernel on [0,1]. Null-mass atoms can be discarded.
This preserves densities, L1 norm and the needed cut bound.

Crucial limit: F is fixed when entering this local region. The unchanged
BUC scope allows F to grow with M or with the number of repetitions. The
argument does not rule out such a construction, small normalizations, other
lifts, or BUC itself. It also does not assert a quantitative growth rate for
the source's sup norm in q; none was proved here.

## 4. What the source supplies and what remains unpaid

Source161 kernel.tex supplies normalized rank-layer indicators, independent
corner coordinates, zero first activation moments, support forcing of one
negative full incidence term, color-refinement type pinning, dilution of the
opposite orientation and a crossed-product symmetrization. The final
normalization scales a nonnegative mean-one kernel by its maximum; it does
not construct complementary colors. Its consequences.tex already supplies
tensor amplification, finite simple hosts and a one-density forcing failure.

The source expansion's nonempty-label propagation and the edge-subset
expansion suggest examining proper edge correlations, but no new uniform
proper-subgraph estimate after bounded normalization is asserted here.
The rank-layer kernel has no supplied uniform bound independent of q.
Simply invoking cancellation before the final bounded scaling does not
control the required weighted sum over all proper even subgraphs afterward.

Kral--Noel--Norin--Volec--Wei Theorem2 and Section4 give some finite k colors
by permutation averaging and replication of a Sidorenko witness. That is a
paid operation, and it does not give k=2. Zhao2606.15368v1 Proposition1.2
attributes to Szegedy a Cayley-host reduction for the strong Sidorenko
inequality; changing to that host class is not a new BUC mechanism either.
Its conjugacy-averaging implication is conditional, not a two-color transfer.

The remaining concrete obligation is a bounded complementary construction
which controls the entire surviving proper-subgraph sum while retaining a
negative full term. A graph gadget could in principle encode the rank-layer
peaks while allowing F to grow, thereby avoiding the fixed-pattern local
barrier. No gadget with exact normalization and control of unintended type
maps was obtained. Adding a universal opposite-part anchor is not a free
pinning operation: it enters a known positive Sidorenko class. No claim that
all gadgets are impossible is made. The full r17 BUC target remains open in
this work; there is no nomination or count increment.
