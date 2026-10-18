# Prescribed trace simplex: an external-primary template already supplies it

Author-side TECHNICAL comparison, no nominee or independent verdict. The
statement contemplated before a freeze was: for every nonempty metrizable
Choquet simplex K, in ZFC construct a unital infinite-dimensional simple
complex C*-algebra A with exactly one equivalence class of nonzero irreducible
representations and T(A) affinely homeomorphic to K. No nuclearity, density
bound, or prescribed representation size is part of that statement.

The following deduction uses Tanaka's existing shell construction. The pinned
source297 is not an essential premise. Consequently this is not eligible as
a substantial source-dependent campaign contribution. No worldwide priority
claim is made for the statement or its presentation.

## Actual comparisons

Pinned297 supplies a reduced HNN bridge joining exactly two old pure-state
classes while uniquely extending EVERY old pure state. Its explicit expectation
onto the peaking algebra D=C*(p_n) is
 E_tau(a)(n)=tau(d_n a d_n)/tau(d_n), d_n=p_n-p_{n+1},
and E_tau(a)(infinity)=f(a). This depends on one faithful trace. Its restriction
and reordering identities make dependency-closed subiterations possible; those
in turn yield countable determination and the ZFC recursion. Replacing CAR
by a multi-trace AF base alone does not establish trace-simplex preservation
for that HNN construction. No impossibility theorem for a different bridge
is inferred from this dependence.

Vaccaro1711.05845v4 explicitly proves the prescribed-simplex result under
diamond (Theorems1–2). Its corrected Theorem A and Lemma3.5 add tracial
strong outerness to an asymptotically inner crossed-product construction.
The pure-state equivalence/unique-extension prescription applies to specified
COUNTABLE families, not every old pure state. Therefore that lemma cannot
simply replace the pinned all-state selective bridge and inherit its
countable-determination theorem. Nuclearity and an M2 embedding in the uniform
tracial central sequence algebra are explicit hypotheses of the trace-homeomorphism
part of Theorem A. We do not silently drop them.

The more decisive comparator is Tanaka2609.26930v1. Its actual Sections2–5
use a concrete atomic representation, partial isometries between projection
shells, and finite generator identities. These operations work for the AF
base constructed below. In particular, approximate innerness, rather than
unique trace or CAR-specific K0, supplies the shell equivalences.

## 1. A standard AF base with uniformly small peaking projections

Use Blackadar's classical realization theorem: every nonempty metrizable
Choquet simplex is T(B0) for a separable simple unital AF algebra B0.
This theorem is an imported standard premise, not reproved here. The original
publisher abstract was read; the complete1980 proof was not read.
Set B=B0 tensor CAR. It is separable, simple, unital, AF and infinite-dimensional.
For every n, traces on B0 tensor M_{2^n} are exactly tau tensor tr_{2^n};
compatibility and density identify T(B) with T(B0), affinely and homeomorphically.
Simplicity follows by viewing B as the unital inductive limit of the simple
matrix algebras M_{2^n}(B0).

Choose increasing finite-dimensional unital subalgebras D_n of B0 with dense
union, and put F_n=D_n tensor M_{2^n}, with the standard unital embeddings.
Use q_0=1 as an initial anchor; minimality below is asserted only for n>=1. Inductively choose a minimal nonzero
projection q_{n+1} of F_{n+1} below q_n. Such a projection exists because
q_n is a nonzero projection in that finite-dimensional algebra. Every matrix
block of F_n has dimension at least2^n. Hence, for every tau in T(B),
 0<tau(q_n)<=2^{-n}.
The strict positivity uses simplicity/faithfulness; only convergence to0 is
needed below. Repeated shell values may be omitted or harmless zero shells
retained; no strict trace decrease is needed in Tanaka's construction.

For n>=1, minimality gives q_n a q_n=f_n(a)q_n for a in F_n. Nestedness makes the f_n
compatible, and they define a state f on B. The q_n peak to f: any state
having value1 on all q_n restricts to f_n on F_n. Thus it is f. The same
argument proves f pure, since every state in a nontrivial convex decomposition
of f would have value1 on all q_n. For a in B, finite-stage approximation gives
 ||q_n a q_n-f(a)q_n|| ->0.
These are exactly Tanaka's compression hypotheses, now with a uniform bound
for ALL traces. No new projection-gluing theorem is needed.

## 2. Existing shell and defect construction

Choose one pure state f_i from each irreducible GNS class of B, including root
r with f_r=f. Kishimoto–Ozawa–Sakai homogeneity supplies approximately inner
automorphisms alpha_i with f_i composed with alpha_i=f; alpha_r=id.
This standard theorem is imported at the exact form stated in Tanaka§2.2.
Put p_{i,n}=alpha_i(q_n), d_n=q_n-q_{n+1}, e_{i,n}=alpha_i(d_n).
Every trace is fixed by approximately inner automorphisms, so
 tau(p_{i,n})=tau(q_n)<=2^{-n} for every tau.

For each i,n, approximate alpha_i(d_n) by u d_n u* within norm<1.
The elementary projection perturbation lemma supplies a unitary v with
v e_{i,n}v*=u d_n u*. Thus w_{i,n}=u* v e_{i,n} satisfies
 w* w=e_{i,n}, ww*=d_n.
For zero shells take w=0; for root i=r take w=d_n. This is precisely Tanaka
Lemma2.2, with no new step. The sums s_{i,N}=sum_{n<N}w_{i,n} satisfy
 s* s=1-p_{i,N}, ss*=1-q_N, ||s_{i,N}||<=1.

Let Pi be the direct sum of one GNS representative pi_i on H_i from each
class, and xi_i its distinguished vector. Projection compression and GNS
uniqueness give, in this atomic representation,
 s-lim Pi(p_{i,n})=projection onto C xi_i.
The limit for q_n is the root rank-one projection. Strong sums of the shell
maps and their adjoints therefore define a partial isometry S_i with those
one-dimensional defects. Add the cross-block rank-one map theta_{xi_r,xi_i}:
 L_i=S_i+theta_{xi_r,xi_i}.
It is unitary. Let A=C*(Pi(B), L_i for all i), with j=Pi|B. All choices are
set-sized. The construction uses only ordinary ZFC choice, as in Tanaka.
Its finite identities, inherited by every representation, are
 L_i(1-j(p_{i,N}))=j(s_{i,N}),
 L_i*(1-j(q_N))=j(s_{i,N})*,
 L_i j(p_{i,N}) L_i*=j(q_N).
Strong-limit pieces are not asserted separately to belong to A.

## 3. The existing arbitrary-representation argument

This is Tanaka§4, with B replacing CAR. The concrete representation is
irreducible: its B-commutant is block-scalar by inequivalence, and commuting
with L_i forces every block scalar to equal the root scalar.

For an arbitrary irreducible rho of A, put sigma=rho composed with j and
P_i=s-lim sigma(p_{i,n}). The finite identities imply
 rho(L_i)=s-lim sigma(s_{i,N})+D_i,
 D_i*D_i=P_i, D_iD_i*=P_r.
If all P_i vanished, the added generators would lie in sigma(B)'', so sigma
would itself be irreducible. Its class occurs among the pi_i, where the
corresponding P_i is nonzero, a contradiction. Thus P_r is nonzero.

Choose a unit eta_r in its range and set eta_i=rho(L_i)*eta_r. These are
unit vectors in P_i with B-vector states f_i. Their B-cyclic subspaces are
pairwise orthogonal copies of the chosen GNS spaces. They give an isometry
W from the atomic H into rho's Hilbert space, intertwining B. On its range,
P_i is the rank-one projection onto eta_i; D_i sends eta_i to eta_r and
vanishes on the other summands. The finite shell sums already intertwine
under W, so taking strong limits and adding these defect formulas shows
W intertwines L_i and L_i* as well. Its range is a nonzero reducing subspace;
irreducibility makes W surjective. Every irreducible representation is thus
equivalent to the faithful concrete one. A proper nonzero ideal would supply
an irreducible quotient representation with nonzero kernel, so A is simple.
It is unital and infinite-dimensional because B is.

## 4. Apply the same trace argument separately to every trace

Fix ANY tau in T(B), and extend it to a state Phi on A by positive state
extension. In the GNS representation rho_Phi, let M be the closed B-cyclic
subspace of its distinguished vector Omega. For b in B,
 ||rho_Phi(j(p_{i,n}))rho_Phi(j(b))Omega||²
   =tau(b* p_{i,n} b)<=||b||² tau(p_{i,n})<=2^{-n}||b||².
The same holds for q_n. Contractivity extends this convergence to M.
The two finite shell identities show that M is invariant under every L_i
and L_i*, hence reduces A. Since it contains Omega, M is the full GNS space.

Identify it with the fixed GNS space of tau on B. On that space every added
unitary MUST act as s-lim pi_tau(s_{i,N}), and its adjoint as the adjoint
strong limit. Thus all state extensions of tau have the same generator
images and the same cyclic vector, so they coincide. This proves unique
STATE extension, stronger than merely a unique tracial extension.

For u unitary in B, conjugating the unique extension by j(u) leaves its
restriction tau unchanged, so B lies in its centralizer. The strong shell
limits show that each L_i lies in the centralizer as well: pass to the limit
in Phi(j(s_{i,N})a)=Phi(a j(s_{i,N})) on the two relevant GNS vectors.
The centralizer is a norm-closed C*-subalgebra, hence all of A. The extension
is tracial and, by simplicity, faithful. This is Tanaka§5 without its final
specialization to the unique trace of CAR.

Consequently restriction T(A)->T(B) is surjective and injective. It is affine
and weak-star continuous. The trace spaces are compact Hausdorff, so this
bijection is an affine homeomorphism. Composing with T(B)≅K proves the
contemplated statement at its full quantifiers.

## Disposition and limits

The extra work is standard AF base preparation and repeating the same trace
proof pointwise in tau. Every hard construction step is Tanaka's existing
operation. The pinned source297 is not needed for this argument. No new
substantial operation, source-dependent theorem, independent proof approval,
or campaign count is claimed. No nuclearity or density conclusion for A is
inferred. This technical derivation is kept to make the exclusion concrete.
