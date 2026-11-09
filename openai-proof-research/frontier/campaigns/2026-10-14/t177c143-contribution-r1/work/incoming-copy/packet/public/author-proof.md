# Author proof at the unchanged T177C143 scope

This is an author proof, conditional only on the stipulated pinned source where that source is explicitly invoked. It is not an independent review or an acceptance. The frozen statement is `frozen-scope.md`, SHA256 cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221. All its quantifiers are retained.

## 1. Incidence identities and the quotient metric

Write mu(v)=w_0(v), nu(e)=w_1(e), and omega(t)=w_2(t). For a vertex v and an edge e, double-counting top-face incidences gives

sum_{e containing v} nu(e)=2mu(v),
sum_{t containing e} omega(t)=3nu(e).                    (1)

All three weight functions sum to one. The second identity gives ||delta_1 x||_2<=3||x||_1: the support of a coboundary is contained in the union of the triangles incident to edges in the support of x. It also gives the exact identity

sum_{e in E} ||delta_1 1_e||_2=3.                        (2)

Purity and d>=2 ensure every edge lies in a triangle, so every delta_1 1_e is nonzero.

The hypothesis H^1(X;F_2)=0 says ker(delta_1)=B^1=im(delta_0). Therefore two preimages of b differ by a cut. The degree-one inequality, applied to any such preimage, says

||b||_2/3 <= lambda(b) <= ||b||_2/beta.                  (3)

The minimum exists because the spaces are finite. Translation invariance makes lambda(b+c) a metric on B. The map b to its 0/1 triangle-coordinate vector, with coordinate t scaled by omega(t), maps into a real L_1 space and has distance ||b+c||_2. Equation (3) proves distortion at most 3/beta, for the entire metric space B.

For any coupling of mu_b and mu_c, every possible difference is a preimage of b+c, so its cost is at least lambda(b+c). Conversely choose a minimum preimage z of b+c. Translation x->x+z is a bijection F_b->F_c and has constant cost lambda(b+c). Coupling a uniform x with x+z proves the asserted exact W_1 identity. This is the finite-group quotient transport operation of Khot–Naor, Lemma3.6, applied with the weighted translation-invariant metric; it is credited support, not the new lower-bound step.

A joint coupling of all mu_b is, almost surely, a section: there are only finitely many b, so the probability-one membership requirements hold simultaneously. In the opposite direction, from any random section s choose an independent uniform U in B^1 and put Z_b=s(b)+U for every b. Each Z_b is uniform on F_b, even conditional on s, and Z_b+Z_c=s(b)+s(c). Thus optimizing over all sections and over all joint uniform-fibre couplings gives identical constants, with either denominator. These operations do not assume pairwise optimal couplings are jointly compatible.

## 2. A Fourier constraint forced by every section

First fix an arbitrary deterministic section s, without normalization or linearity. For x in the full edge cube F_2^E put

q(x)=x+s(delta_1 x).

Its coboundary is zero, hence q(x) is a cut. More importantly, for every vertex cochain a,

q(x+delta_0 a)=q(x)+delta_0 a.                           (4)

For each ordered pair u,v, let F_uv(x) in {+1,-1} be the sign of the potential difference between u and v of this cut. More explicitly, take any edge path P_uv from u to v and set

F_uv(x)=(-1)^{sum_{e in P_uv}q(x)_e}.

For a cut this is independent of the chosen path. Set F_uu=1. Equation (4) yields

F_uv(x+delta_0 a)=(-1)^{a(u)+a(v)}F_uv(x).                (5)

Let chi_A(x)=(-1)^{sum_{e in A}x_e}, for A subset E, be the normalized Walsh characters under uniform x. Translating the Fourier coefficient of F_uv by delta_0 a shows that a nonzero coefficient at A requires

sum_{e in A}(delta_0 a)_e=a(u)+a(v) for every a.

Equivalently the odd-degree vertex set of the subgraph (V,A) is {u,v} when u!=v, and empty when u=v. For u!=v, the component containing u must contain another odd-degree vertex by the handshaking identity, and that vertex must be v. Thus A contains a u-v path and

|A|>=dist_G(u,v).                                       (6)

This is a character-coset variant of the classical Fourier support restriction. The translation identity (5), rather than invariance of s itself, is essential: s is arbitrary and need not be linear or equivariant.

For a Boolean sign function F, write I_e(F)=Pr_x[F(x+1_e)!=F(x)]. Orthogonality gives

I_e(F)=sum_{A containing e} hat F(A)^2,
sum_e I_e(F)=sum_A |A|hat F(A)^2.

For clarity, the first equality follows by expanding E(F(x+1_e)-F(x))^2/4; Parseval gives sum_A hat F(A)^2=1. Combining with (6), and including u=v trivially, yields

sum_e I_e(F_uv)>=dist_G(u,v).                            (7)

The Parseval/influence step and support restriction are classical Fourier operations, as in Khot–Naor Lemmas2.1 and3.3. The section-dependent character cosets in (5) are what connect those operations to this filling problem.

## 3. Converting the character constraint into the full lower bound

Fix x and e. The difference q(x+1_e)+q(x) is a cut. Choose either vertex potential a for this cut and let t=||a||_0. Independent ordered vertices u,v sampled with law mu have different a-values with probability 2t(1-t). This quantity is independent of replacing a by a+1. Consequently

sum_{u,v}mu(u)mu(v) 1{F_uv(x+1_e)!=F_uv(x)}
 =2t(1-t)
 <=2 min(t,1-t)
 <=(2/alpha)||q(x+1_e)+q(x)||_1.                         (8)

The last step is the given degree-zero expansion. Since

q(x+1_e)+q(x)=1_e+s(delta_1 x+delta_1 1_e)+s(delta_1 x),

the support triangle inequality bounds its norm by nu(e) plus the corresponding section difference. Sum (8) over e and average uniform x. The linear map delta_1 sends uniform x to uniform b in B, because all its fibres have the same cardinality. Averaging (7) over u,v now gives

bar_d <= (2/alpha)[1+sum_e E_{b uniform B}||s(b+delta_1 1_e)+s(b)||_1].

This proves (B) for each deterministic s. Averaging over ANY distribution of s proves it for every stochastic section. The same fixed sum over (b,e) is used before averaging over s; hence the bad pair extracted below does not depend on the realized random seed.

If L_s is the maximum syndrome-normalized expected distortion of that distribution, (2) bounds the sum on the left of (B) by 3L_s. If R_s is its lambda-normalized maximum, lambda(delta_1 1_e)<=nu(e) bounds the sum by R_s. Hence

L_s>=(alpha bar_d-2)/6,
R_s>=alpha bar_d/2-1.

Taking the infima proves both lower bounds in (A). In particular the lower statement covers arbitrary nonlinear maps, arbitrary randomness and every possible grand coupling. It is not merely a failure of linear inversion or of one chosen estimator.

## 4. A single random linear section for every pair

Choose a rooted breadth-first spanning tree T of G. For each b choose any preimage x. There is a unique cut delta_0 a whose restriction to T equals x restricted to T: solve for a along the tree, fixing its root value to zero. Define

s_T(b)=x+delta_0 a.

Changing x by any cut changes a by its corresponding potential modulo constants, so s_T is well-defined. It is F_2-linear, is a right inverse of delta_1, and its output vanishes on T. For an output edge f outside T, the value of s_T(delta_1 x) on f is the parity of x along the fundamental cycle C_T(f); output tree edges are zero.

The tree has depth at most D_G, so every such cycle has at most 2D_G+1 edges. Interchanging the two finite sums gives

sum_{e in E}||s_T(delta_1 1_e)||_1
 =sum_{f outside T}nu(f)|C_T(f)|
 <=2D_G+1.                                               (9)

This identity needs neither short triangle fillings of the cycles nor an efficient choice of syndrome preimage.

Choose g uniformly from H and conjugate the section by g. Automorphisms preserve all incidence weights and commute with delta. For an edge e in orbit O,

E_g||s_g(delta_1 1_e)||_1
 =(1/|O|)sum_{a in O}||s_T(delta_1 1_a)||_1
 <=(2D_G+1)/|O|
 <=[(2D_G+1)/gamma]nu(e).                                (10)

The last step uses |O|nu(e)=nu(O)>=gamma. If x is a minimum-norm preimage of b+c, linearity and the support triangle inequality give

E_g||s_g(b)+s_g(c)||_1
 <=sum_{e in supp x} E_g||s_g(delta_1 1_e)||_1
 <=[(2D_G+1)/gamma]lambda(b+c).

This holds for all pairs under ONE distribution on linear sections. Equation (3) finishes both upper bounds in (A). The fundamental-tree gauge is classical; group averaging and incidence counting are paid operations, closely related to the actual random-cone proof of Kaufman–Oppenheim Theorem3.8 and Wild Proposition3.13. The proposed contribution does not rest on calling averaging a new mechanism.

## 5. Uniform constants for every source level

Use the exact source177 construction and the symbols of the frozen statement. The source's thm:main, prop:quotient-homology and its assembly supply connectedness, H^1(X_m;F_2)=0, and alpha=beta=epsilon. Its degree formula gives at most D top faces through each vertex. Its construction and lem:patterns give the action of G_m=U/Gamma_N(m), transitive on faces of each type, with every nonempty face stabilizer a subgroup of a vertex stabilizer of order M. Its growth formula gives n_m tending to infinity. These source statements AND proof operations are stipulated true; no truth audit is made.

For any pure d-complex with n vertices and this vertex-incidence bound, if f_d is the number of top faces then

n/(d+1)<=f_d<=Dn/(d+1),
1/(Dn)<=mu(v)<=D/n,
max degree(G)<=Delta=dD.                                 (11)

There are at most binom(N,d+1)|G_m| d-faces in X_m, by counting them in the ambient chambers. Each edge-type orbit has size at least |G_m|/M, and each edge has w_1(e)>=1/[binom(d+1,2)f_d]. Hence every such orbit has total weight at least 1/K. This is an actual source action on the unchanged complex, not an assumed transitive action on all edges. We may use H equal to its image in Aut(X_m), giving gamma>=1/K.

For the diameter, a vertex set S of mu-mass at most 1/2 has crossing-edge mass at least epsilon mu(S). Every crossing edge has its outside endpoint in N(S) minus S. Equation (1) shows

mu(N(S) minus S)>=epsilon mu(S)/2.

Thus graph balls grow in mu-mass by at least 1+epsilon/2 while their mass is at most 1/2. Starting at mass at least 1/(Dn), a ball of radius

R=ceil(log(Dn)/log(1+epsilon/2))+1

must have mass greater than 1/2. Any two such balls intersect, so D_G<=2R. This proves the diameter estimate at every level, without assuming regularity.

For the mean distance, a graph of maximum degree at most Delta>=2 has at most sum_{j=0}^{r-1}Delta^j<=Delta^r vertices in a ball of radius r-1. If r=r_m>=1, its mu-mass is at most (D/n)Delta^r<=1/2 by the definition of r_m. Conditional on any first vertex u, a second independent vertex has distance at least r with probability at least 1/2. Therefore bar_d>=r/2. For r=0 the same inequality is immediate. Substituting gamma>=1/K, D_G<=2R and bar_d>=r/2 into (A) proves EVERY inequality in (C).

For fixed d,q, all D,Delta,K,epsilon are fixed, Delta>=2, and n_m tends to infinity. The integer r_m grows proportionally to log n_m and R_m is O(log n_m). The positive logarithmic terms eventually dominate the finite subtracted constants. Thus both infima have exactly logarithmic order, with constants depending only on d,q. The all-level finite bounds are retained, including levels where their lower sides are nonpositive.

## 6. Scope and relation to the exploratory lead

Coefficient-uniform cosystolic expansion in Oppenheim–Valentiner-Branth Theorem1.2 applies to F_2^r with constants independent of r. The source's F_2 vanishing implies F_2^r vanishing by taking direct sums, and its skeleton-weight comparison is valid for vector labels because the norm measures nonzero support. Packing any finite family of cochains into one vector-valued cochain therefore supplies union-of-support collective cofilling. This is credited source/primary support, consistent with Kaufman–Tessler's definition; it is not this theorem's nomination.

Collective filling chooses lifts for a given family under a union-support objective. Pairwise optimal transport chooses a coupling separately for each pair. The frozen theorem instead measures one jointly chosen family of lifts against every pair simultaneously. Sections can have constant norm control relative to zero and still fail that stronger condition. No impossibility of ordinary filling, collective filling, or pairwise optimal transport has been asserted.

The decisive lower step is the full-section identity (4), its vertex-pair character cosets, and the conversion of their minimum path lengths into (B) using graph expansion. The classical Fourier and averaging ingredients are explicit. Whether this operation warrants a substantial-contribution judgment is left entirely to separate review with the actual primary bodies. No worldwide-priority or literature-exhaustion claim is made.
