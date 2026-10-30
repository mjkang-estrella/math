# Author proof of the frozen R162CP statement

This proves the unchanged statement in STATEMENT.md relative to the stipulated Source177 operations. It is an author proof submitted for independent review, not a correctness or contribution verdict. Write X=X_m, V=V_m, G=G_m, M=q^(binom(N,2)), and F=|X(d)|. All vector operations below are over F_2 unless real weights or real Fourier coefficients are explicitly involved. Fix epsilon as in the frozen statement.

## 1. Exact source interfaces and weighted identities

Source177, construction.tex, equation (construction), supplies precisely X=skel_d CC(G;(H_i)). Its geometry.tex local-pattern lemma and expansion.tex, “Degree bounds and growth,” supply the following facts: X is finite, pure and connected; every vertex is in at most D=M binom(N-1,d) top faces; V=N|G|/M tends to infinity with m; and G acts by type-preserving simplicial automorphisms. For a nonempty type set A subset {0,...,N-1}, the faces of type A are one G-orbit, of cardinality |G|/c_A, where c_A=|U_(S\A)| is independent of m and 1<=c_A<=M. The action is on the original tagged cosets, hence does not identify vertices of different types. The source's homology-comparisons and quotient-homology propositions, followed by its main theorem, give

  ker delta_1=im delta_0,
  ||delta_0 h||_1 >= epsilon min{||h||_0,1-||h||_0},                 (1)
  ||delta_1 f||_2 >= epsilon dist_1(f,im delta_0).                 (2)

These are stipulated source facts, not conclusions of a new audit. Only degrees zero and one are used here; all stronger source and companion operations remain paid.

The intrinsic weights of X sum to one in each degree. Double counting incidences gives, exactly,

  sum_(e containing v) w_1(e)=2w_0(v),
  sum_(tau in X(2), tau containing e) w_2(tau)=3w_1(e).           (3)

For example, every d-face through a given edge contains d-1 triangles through that edge, and (d-1)/binom(d+1,3)=3/binom(d+1,2). Thus

  ||delta_1 f||_2 <= 3||f||_1,
  sum_(e in X(1)) ||delta_1 1_e||_2=3.                           (4)

The first inequality uses the ordinary union bound for the support of a sum in F_2. In the second identity each triangle is counted once for each of its three edges. Every edge belongs to a triangle by purity, so each delta_1 1_e is nonzero; duplicated syndrome directions, if any, are still counted with their original edge multiplicities.

Write H for the simple graph X^(1), and d_H for its graph distance. Put Delta=dD and B=Delta+1. Purity implies degree_H(v)<=Delta. Also V<=(d+1)F<=DV, and hence

  1/(DV) <= w_0(v) <= D/V.                                     (5)

No uniform replacement for w_0 or w_1 has been made.

We will also need a lower bound on the weight of each edge orbit. Put b=binom(d+1,2) and K=binom(N,d+1). If O_A is the orbit of edges of type A, |A|=2, then

  alpha_A := sum_(e in O_A) w_1(e)
           = [sum_(B' containing A, |B'|=d+1) 1/c_(B')]
             /[b sum_(|B'|=d+1) 1/c_(B')].                     (6)

Indeed a fixed type-A edge has c_A/c_(B') containing type-B' d-faces, and F=|G| sum_(|B'|=d+1)1/c_(B'). Equation (6) follows after multiplying its weight by |G|/c_A. In particular

  alpha:=min_(|A|=2) alpha_A >= 1/(M b K)>0.                    (7)

All these quantities except V,F,|G| are fixed once d,q are fixed. The group action preserves exactly the intrinsic weights.

## 2. Pairwise optimal transport is already paid

Let z,z' be any two syndromes. In every coupling of mu_z and mu_(z'), each realized difference f+f' is a primitive of z+z'. Its norm is at least Q_m(z+z'). Conversely choose a minimizing primitive a of z+z'. If f is uniform on F_z, then f+a is uniform on F_(z'), and the cost is constantly ||a||_1. This proves

  W_1(mu_z,mu_(z'))=Q_m(z+z').                                  (8)

This is the finite additive special case of Khot--Naor, Lemma 3.6, whose actual proof was read. We claim no additional contribution for it.

Since ker delta_1=im delta_0, every fiber is a coset of im delta_0. Thus (2), applied to any member of the fiber, gives Q_m(z)<=epsilon^(-1)||z||_2. Equation (4) gives Q_m(z)>=||z||_2/3. These statements include z=0, where both sides vanish, and prove all the frozen two-law assertions.

## 3. An affine Fourier constraint for EVERY section

Fix an arbitrary section s. No linearity, continuity, marginal condition or normalization at zero is assumed. On the whole cube C^1=F_2^(X(1)) define

  P_s(f)=f+s(delta_1 f).

It lies in ker delta_1=im delta_0. Fix a root vertex o. By connectivity there is a unique g(f) in F_2^(X(0)) with g(f)(o)=0 and delta_0 g(f)=P_s(f). For every vertex cochain h we have

  P_s(f+delta_0 h)=P_s(f)+delta_0 h,
  g(f+delta_0 h)=g(f)+h+h(o)1.                                 (9)

The first identity uses only delta_1 delta_0=0 and the fact that s is a single function on all syndromes. The second follows by taking the rooted representative. In particular for each ordered pair of vertices u,v the real-valued sign

  chi_(u,v)(f)=(-1)^(g(f)(u)+g(f)(v))

obeys

  chi_(u,v)(f+delta_0 h)=(-1)^(h(u)+h(v)) chi_(u,v)(f).          (10)

Expand chi in the orthonormal Walsh characters on the uniform edge cube:

  chi(f)=sum_(A subset X(1)) hat(chi)(A) (-1)^(sum_(e in A) f(e)).

Changing variables f to f+delta_0 h in the coefficient shows that a nonzero coefficient is possible only if, for every h,

  sum_(e in A) (delta_0 h)(e)=h(u)+h(v).

The left side is the sum of h over the odd-degree vertices of the edge subgraph A. Therefore

  hat(chi_(u,v))(A)!=0 ==> partial A=1_u+1_v.                  (11)

For u!=v, every graph with exactly those two odd vertices contains a u-to-v path: each connected component has an even number of odd-degree vertices. Consequently |A|>=d_H(u,v). For u=v the same inequality is trivial.

Parseval and the single-bit derivative identity give

  sum_e Pr_f[chi_(u,v)(f+1_e)!=chi_(u,v)(f)]
    =sum_A |A| hat(chi_(u,v))(A)^2
    >=d_H(u,v),                                               (12)

because chi takes values in {+1,-1} and so sum_A hat(chi)(A)^2=1. For completeness, the derivative identity follows from orthogonality:

  E_f[(chi(f+1_e)-chi(f))^2]/4
     =sum_(A containing e) hat(chi)(A)^2.

The left side is the probability of a sign change. The covariance in (10), rather than invariance under cuts, is essential: the support is an affine boundary class with endpoints u,v. Standard invariant quotient characters instead have empty boundary. No linearity of the original section has entered this calculation.

## 4. Original weighted expansion forces average sensitivity

Define the weighted average graph distance

  Dbar=sum_(u,v) w_0(u)w_0(v)d_H(u,v).

For each f,e put h_(f,e)=g(f)+g(f+1_e), a vertex cochain. If t=||h_(f,e)||_0, then

  sum_(u,v) w_0(u)w_0(v) 1{h_(f,e)(u)!=h_(f,e)(v)}
    =2t(1-t) <=2min(t,1-t) <=(2/epsilon)||delta_0 h_(f,e)||_1,   (13)

where the last inequality is (1). On the other hand

  delta_0 h_(f,e)=1_e+s(delta_1 f)+s(delta_1 f+delta_1 1_e).

Use (12), average over vertices, then use (13), the triangle inequality, and sum_e w_1(e)=1. The image of a uniform f under the surjective linear map delta_1:C^1->Z_m is uniform on Z_m, because all its fibers have equal cardinality. We obtain

  Dbar <= (2/epsilon)
       [1+sum_e E_(z uniform Z_m)||s(z+delta_1 1_e)+s(z)||_1].   (14)

This same inequality remains true after averaging over ANY probability law P on the finite set of sections. If L=L_m(P), the sum in (14) is at most

  L sum_e ||delta_1 1_e||_2=3L.

Hence every such law, without any marginal constraint, satisfies

  L_m(P) >= epsilon Dbar/6 - 1/3.                              (15)

The expectation and the maximum have not been interchanged. The bound on each fixed pair follows from the definition of L; (14) then averages those bounds. It follows in particular that some fixed pair has large expected cost for each entire law P. The argument does not merely choose a different pair after seeing the random section.

To estimate Dbar use the degree bound. A radius-r graph ball has at most B^(r+1) vertices, so by (5) its w_0-mass is at most D B^(r+1)/V. For sufficiently large V set

  r=floor(log(V/(2D))/log B)-1 >=0.

Every such ball then has mass at most 1/2. For every u, at least half the vertex mass has distance greater than r, whence Dbar>=r/2. Once log V>=2log(2D)+4log B we have r>=log V/(2log B). Thus

  Dbar >= log V/(4log B).

If also log V>=16log B/epsilon, (15) implies

  L_m(P) >= [epsilon/(48log B)] log V                         (16)

for EVERY law P. Source growth V_m->infinity gives one m_0 after which both numerical conditions hold for all m. This proves the lower bound on S_m and, a fortiori, U_m. It is a true universal obstruction for the stated global-selection problem, with no claim about a different algorithmic task.

## 5. A logarithmic-radius tree in the SAME graph

We need a radius estimate in the original weights. Let S be a vertex set with w_0(S)<=1/2. From (1), the total w_1-weight of its crossing edges is at least epsilon w_0(S). Each crossing edge is incident to N_H(S)\S. The first identity in (3) therefore gives

  w_0(N_H(S)\S) >= (epsilon/2)w_0(S).                          (17)

Starting from any vertex, whose mass is at least 1/(DV), successive balls grow by factor at least 1+epsilon/2 until their mass exceeds 1/2. Put

  k=ceil(log(DV)/log(1+epsilon/2))+1.

A ball of radius k must have mass greater than 1/2: if all preceding balls had mass at most 1/2, (17) would give mass greater than 1 at radius k. Two radius-k balls therefore intersect. The graph diameter is at most 2k. Choose a breadth-first spanning tree T rooted at o. Its root radius R is at most 2k.

## 6. Tree gauge, orbit averaging and one uniform cut

For f in C^1 define h_T(f)(v) to be the sum of f on the unique tree path from o to v. It is F_2-linear in f. Set

  Q_T f=f+delta_0 h_T(f).

This output is zero on every edge of T, delta_1 Q_T f=delta_1 f, and Q_T delta_0 h=0 for every h: the tree path sum of delta_0 h is h(v)+h(o). Thus Q_T kills exactly the ambiguity relevant to primitive choice, and

  s_T(z)=Q_T f, where delta_1 f=z,                            (18)

is a well-defined linear section. Equivalently it is the unique primitive that vanishes on T.

For an output edge b={u,v}, the coordinate (Q_T f)(b) is the parity of f on

  C_b={b} symmetric-difference path_T(u,v).

For a tree edge this set is empty. For every other edge it has at most 2R+1 members. Hence its total weighted column mass is

  sum_(e in X(1)) ||Q_T 1_e||_1
    =sum_(b in X(1)) w_1(b)|C_b| <=2R+1.                     (19)

This identity is a row-column double count, not a bound on each column of a fixed tree.

For gamma uniform in G let Q_gamma=gamma Q_T gamma^(-1). The action on cochains is the induced permutation action; it commutes with the coboundary maps and preserves all the intrinsic weights. If e has type A, gamma^(-1)e is uniform on O_A. Therefore (19) implies

  E_gamma ||Q_gamma 1_e||_1
    =|O_A|^(-1) sum_(a in O_A)||Q_T 1_a||_1
    <=(2R+1)/|O_A|
    =[(2R+1)/alpha_A] w_1(e)
    <=K_m w_1(e),   K_m:=(2R+1)/alpha.                       (20)

By linearity and the support union bound, for EVERY f in C^1,

  E_gamma ||Q_gamma f||_1 <= K_m ||f||_1.                     (21)

Define s_gamma on syndromes by (18) with Q_gamma in place of Q_T. It is again a linear section. For any two z,z', take a minimum-norm primitive a of z+z'. Since s_gamma is linear and independent of the choice of primitive,

  E_gamma ||s_gamma(z)+s_gamma(z')||_1
     =E_gamma ||Q_gamma a||_1
     <=K_m Q_m(z+z')
     <=K_m epsilon^(-1)||z+z'||_2.                           (22)

Choosing a separately for each pair in this proof does NOT alter the constructed common section. The sections were already defined by a tree and gamma for the whole domain; the minimizing a is used only to estimate their difference.

Now choose a single independent b uniformly from im delta_0 and set

  s_(gamma,b)(z)=s_gamma(z)+b FOR EVERY z.

For each fixed gamma,z, translation by the uniform cut gives exactly the uniform law on F_z, since F_z=s_gamma(z)+im delta_0. Consequently this is one joint coupling of all the required laws. Its pair differences agree exactly with those of s_gamma, because the SAME b is added to both outputs. Its sections are affine. The linear law has support at most |G|, and the affine law at most |G|2^(V-1). There is no dependence of the seed on the queried syndrome.

Since alpha has the fixed lower bound (7), and R<=2k=O_(d,q)(log V), we have K_m<=C_0 log V for V>=2, with C_0 depending only on d,q. Equation (22) yields U_m<=C_0 epsilon^(-1) log V and S_m<=U_m, with the asserted linear upper witness for S_m. Dividing (22) by (8) gives R_m<=C_0 log V.

Finally, for any prescribed-marginal law P,

  max_(z!=z') E||s(z)+s(z')||_1/Q_m(z+z') >= epsilon L_m(P),

by Q_m(z+z')<=epsilon^(-1)||z+z'||_2. Thus (16) gives the lower bound for R_m. One may take the common lower constant c=epsilon^2/(48log B); take C large enough for the two upper estimates. All constants and the threshold m_0 precede m and every choice of sections or laws. This completes the entire frozen theorem.

To make the parameter dependence entirely explicit, for each d,q one can select once the specific positive constant supplied by Source177, min{1,eta/M}, and use that constant in Sections 1 and 3–6 to select c,C,m_0. The asymptotic conclusions thus depend only on d,q, independently of how a valid constant epsilon is presented in the frozen two-law inequalities. Section 2 proves those two-law inequalities separately for ANY chosen common epsilon. If that chosen value differs from the fixed source value, the asymptotic argument is simply run with the fixed source value; it does not require a new hypothesis or change of family.

## 7. Costs, scope and what is not implicit

The theorem makes no computational complexity assertion. Nevertheless the upper construction uses no uncharged table over all syndromes. On an explicitly supplied complex, compute a BFS tree from its edge incidence list. A rooted potential and Q_T f can be evaluated by tree traversal and edge scans. To evaluate the section on z, solve delta_1 f=z by ordinary F_2 elimination and apply Q_gamma. Alternatively solve the unique system delta_1 f=z, f|_(gamma T)=0 directly. Existence and uniqueness were proved above.

Given a labelled explicit incidence structure and the explicit list of the |G| vertex permutations from the group action, all these operations, parsing, checking incidences, finite-field elimination, permutation lookup, and writing the entire edge-cochain output take a polynomial number of bit operations in the total explicit input length. This statement can be implemented by elementary scans and Boolean elimination; it does not assume a free linear-algebra oracle. For fixed d,q, there are O_(d,q)(V) faces in each relevant degree and |G|=MV/N, so even the whole permutation list and the list of |G| section matrices have polynomial size in V. No full source group/complex generator was executed here, and no jointly efficient construction as d,q vary is asserted.

A uniform cut can be generated by V-1 independent unbiased vertex bits with the root fixed to zero. A uniform index gamma among |G| listed elements can be sampled by rejection from ceil(log_2|G|) bits; it uses fewer than two trials in expectation (the trivial |G|=1 case needs none). The number of trials has no deterministic bound. Once gamma and the common cut are drawn, every subsequent evaluation is deterministic with that same seed. Materializing all outputs for all z would require their actual exponentially large output size; the theorem never gives such materialization for free. The lower bound is on the pairwise sensitivity of a single common choice, not on the time, space, randomness or correctness of solving an individual primitive problem.
