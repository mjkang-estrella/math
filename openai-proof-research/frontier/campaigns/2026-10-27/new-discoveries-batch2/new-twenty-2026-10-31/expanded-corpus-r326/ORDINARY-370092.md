# 370092: complete ordinary refutation, qualification HOLD

Credit 0. Not accepted, source-qualified, independently reviewed, or formalized. No Pi implementation plan is authorized by this packet. The following is an ordinary proof of the negation of the **general finite irreducible matrix-group version** literally included in the reserved record. It does not refute a restriction to quaternionic reflection groups. Root must adjudicate this scope distinction before any execution.

## Exact source scope

The full literal statement, raw newline, source path and hashes are in provenance.json and raw/370092.jsonl. Buckley–Waldron arXiv:2509.01859v1, Section 6 Conjecture 1 says the maximal reducible subgroups of every quaternionic reflection group, “or every finite irreducible group” of quaternionic matrices, fix finitely many lines. Here “fix a line” is setwise/projective stabilization, not fixing every vector. The paper's Section 5 equations (5.31), Examples 5.3–5.4 and Table 3 use this projective meaning. The pointwise stabilizer is expressly distinguished immediately before Section 6. This distinction is essential: the subgroup below has no common fixed nonzero vector.

The public arXiv version page retrieved 2026-11-06 exposes only v1, submitted 2025-09-02 00:56:42 UTC. Search-indexed primary journal material identifies Electronic Journal of Linear Algebra volume 42, pp. 1–20, January 2026, and repeats Conjecture 1's broad quantifier. The direct journal PDF GET ended with a closed connection. Its complete latest proof body is UNREAD; no retry or alternate access was attempted. The claim is therefore qualification HOLD. Search snippets are not full proof-body review.

## Construction

Work in the right vector space V = H^2 with quaternionic matrices acting on the left. Let Q = {1,-1,i,-i,j,-j,k,-k}, the quaternion group under multiplication, and D(q)=diag(q,q). Put c=-1/2 and s=sqrt(3)/2, and let

R = ((c,-s),(s,c)),   H = {D(q):q in Q},
G = {D(q) R^a : q in Q, a in {0,1,2}}.

All entries of R are real, so R commutes with every D(q). Since c^2+s^2=1, c^2-s^2=c and 2cs=-s, multiplication gives
R^2=((c,s),(-s,c)) and R^3=I. Neither R nor R^2 is diagonal since s>0. Thus the three cosets H, HR, HR^2 are disjoint, with eight distinct elements each. Multiplication and inversion preserve the displayed set, so G is a finite subgroup of GL_2(H), indeed of the quaternionic unitary group, of order 24. H is a subgroup of order 8. Unitarity follows from |q|=1 and R^t R=I.

## The H-invariant lines

Every right quaternionic line other than the vertical line has a unique normalized generator (1,t), t in H. If its generator was (x,y) with x nonzero, multiply on the right by x^{-1}, yielding t=y x^{-1}.

Invariance under D(i) implies (i,it)=(1,t)a for some quaternion a. First coordinates force a=i, hence it=ti. Similarly D(j) implies jt=tj. Write t=t0+t1 i+t2 j+t3 k with real coefficients. Commuting with i forces t2=t3=0; commuting with j then forces t1=0. Thus t is real. Conversely, any real t commutes with every q in Q, so D(q)(1,t)=(1,t)q. The vertical line (0,1)H is also invariant. Hence the invariant lines are exactly

L_t=(1,t)H for t in R, together with L_infinity=(0,1)H.

Distinct real parameters give distinct right quaternionic subspaces: if (1,t)=(1,u)a, the first coordinate gives a=1 and the second gives t=u. In particular, the lines L_n for natural n already form an infinite family. H is reducible, as it preserves the nonzero proper horizontal line L_0.

## G is irreducible

A nonzero proper right H-subspace of H^2 has dimension one. Thus any such G-invariant subspace would be one of the lines just classified. The vertical line is not R-invariant because R(0,1)=(-s,c) has nonzero first coordinate.

For t real, R(1,t)=(c-st,s+ct). If L_t were invariant, first-coordinate comparison forces its right multiplier to equal c-st. The second coordinate would require

s+ct=t(c-st)=ct-st^2,

so s(1+t^2)=0. This is impossible over the reals because s>0 and 1+t^2>0. (The same equation also covers c-st=0 without division.) There is no nonzero proper invariant quaternionic subspace. G is irreducible in precisely the quaternionic sense, not merely in a real or complex restriction.

## H is maximal reducible

If H < K <= G is any subgroup, pick g in K outside H. Its displayed form is D(q)R or D(q)R^2. Since D(q) is in H, K contains R or R^2; in the latter case it contains (R^2)^2=R. Hence K contains H and R, which generate G. Thus K=G. Since G is irreducible and H reducible, H is maximal among reducible subgroups. No subgroup classification or enumeration is involved.

Combining these facts, G is a finite irreducible quaternionic matrix group with a maximal reducible subgroup H fixing infinitely many lines. This negates the broad literal assertion of 370092.

## Objection checks and scientific limits

1. Finiteness of G does not imply finiteness of invariant subspaces; here each fixed group element acts on every L_t by a parameter-dependent right scalar.
2. The nonmaximal continuous family in source Example 5.3 alone is insufficient. The new step here is adjoining the commuting order-three real rotation and proving maximality directly.
3. The related author manuscript The geometry of the six quaternionic equiangular lines, Section 6, specifies a multiplicity-one one-dimensional submodule when producing a finite class of lines. H here acts as two equivalent copies of its defining quaternionic module, so that condition fails. The companion's result does not prove the conjecture and does not directly give this G/H counterexample. Its representation-theoretic ingredients are classical; bounded search does not establish literature novelty or significance.
4. This is not a counterexample to the reflection-group-only question. No such conclusion, or solution of a repaired restricted question, is claimed. The reserved record explicitly includes finite irreducible groups; root must rule whether the general version merits the requested credit.
5. No upstream OpenAI theorem is used. Every mathematical deduction above is given explicitly. No solver, CAS, enumeration or numerical evidence was used.
6. Latest journal body, complete predecessor/companion and citing-body coverage, adversarial review and global priority remain unresolved. These block source qualification and execution routing even though the ordinary mathematics is complete.

## Semantic endpoint specification (not an implementation plan)

Use V=(Fin 2 -> Quaternion R) with its right quaternionic module structure, or equivalently a left module over the opposite division ring. A line is an actual one-dimensional right submodule, not a chosen vector, real plane, or list of orbit representatives. Matrix invariance means forall g in subgroup and v in W, g*v belongs to W. Define reducible as existence of a submodule W with W nonzero and W not top; define maximal reducible by reducibility plus every strictly containing subgroup being irreducible. Define FixedLines(H) as the set of invariant one-dimensional right submodules. The exact eventual endpoint is existence of a finite matrix subgroup G, irreducible on V, and a maximal reducible H <= G for which FixedLines(H) is infinite; this implies the negation of the universal finite-group formulation.

Required semantic bridges include actual right-submodule invariance, normalization by x^{-1} on the right, quaternion coordinate centralizer calculation, dimension-two proper-subspace classification, actual matrix subgroup closure/finiteness, maximality among all subgroups (not merely a supplied list), and injectivity of n -> L_n into distinct subspaces. A theorem merely about formal triples (q,a), or a finite array of matrices without these bridges, is insufficient. No Lean endpoint exists in this lane. No dormant Pi execution plan is supplied while source qualification is HOLD. If root later qualifies the result, execution requires its separate authorization and the mandated Pi model; acceptance still needs all independent review, paper, axiom and extracted replay gates.
