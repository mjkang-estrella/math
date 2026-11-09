# MathDB318479: ordinary proof of translated degree preservation

Status: complete ordinary argument, personally derived from the primary tableau definition and checked below. This is not an acceptance, formal certificate, or assertion of literature priority. Final journal equivalence remains unverified. No mathematical program was used.

## Exact endpoint and conventions

For six partitions a=(lambda,mu,nu), b=(lambda',mu',nu'), write c(a)=c(lambda;mu,nu), with lambda the OUTER shape, mu the inner shape, and nu the content. Parts are nonnegative integers, weakly decreasing, with finitely many positive parts; trailing zeros do not matter. Addition and stretching are componentwise. Suppose the function f(n)=c(na) agrees, for positive integers n, with a NONZERO polynomial of finite degree d, and c(b)>0. Then c(na+b) agrees for every sufficiently large integer n with a nonzero polynomial g of degree d. An integer threshold can be increased to a positive integer; then P(m)=g(m). If c(a)=1, the primary Fulton theorem makes f identically one, and consequently P(n)=P(m) for n>=m.

The usual degree of the zero polynomial is not a finite integer d. We do not silently use a programming library's natDegree(0)=0. If the source includes n=0 in its polynomial premise, that is stronger and the same proof applies. The proof requires no assertion that an incompatible zero sequence on positive n also has value zero at n=0: the all-empty triple has coefficient one. This disposes of the convention trap without changing the intended nonzero source context (Section5 explicitly starts with both coefficients nonzero).

## 1. A complete fixed lattice model from the source definition

Choose k>=1 at least all six lengths and pad by zeros. For a triple (L,M,N), let Q(L,M,N) in R^(k*k) consist of arrays x_(r,j), 1<=r,j<=k, satisfying:

(A) x_(r,j)>=0.
(B) sum_j x_(r,j)=L_r-M_r, and sum_r x_(r,j)=N_j.
(C) M_r+sum_(j<=t) x_(r,j) <= M_(r-1)+sum_(j<t) x_(r-1,j), for 2<=r<=k, 1<=t<=k.
(D) sum_(r<s) x_(r,j) >= sum_(r<=s) x_(r,j+1), for 1<=s<=k, 1<=j<k.

All equations/inequalities have a fixed integer matrix. Their right sides are linear in L,M,N. Equations can be replaced by opposite inequalities. Thus Q(na+b)={x:Ax<=n u+v} for fixed integral A,u,v; Q(na)=n Q(a) for n>0.

Here is the exact bijection, rather than a model-name appeal. An LR tableau gives x_(r,j) as the number of entries j in row r. Conversely put x_(r,j) copies of j in increasing order in row r, starting at column M_r+1. Row lengths and content are (B), and the row order is unique. For a lower row r, its entries <=t end at column M_r+sum_(j<=t)x_(r,j). The upper row's entries <t, together with its missing initial M_(r-1) boxes, end at column M_(r-1)+sum_(j<t)x_(r-1,j). Because M_(r-1)>=M_r and L_(r-1)>=L_r, comparison of these endpoints for every t is exactly strict increase wherever both rows have a box. If a lower endpoint is within the missing initial upper segment, there is no column condition there and (C) holds automatically. For a lower entry t beyond that segment, (C) says that the entry above it is <t. Necessity follows by looking at the last lower entry <=t; sufficiency follows by looking at the last lower occurrence of each actual value t. This proves (C) in both directions, including empty rows.

Read each row right to left and the rows top to bottom, as in the source. For the pair j,j+1, the most adverse prefix within row s occurs after all entries j+1 in that row and before any entries j. Thus the lattice-word condition at every prefix is equivalent to (D). Entries other than j,j+1 do not change their difference. Consequently integer arrays in Q correspond bijectively to the source's LR tableaux. The finite alphabet is exact because the content has length <=k; entries >k cannot occur. No triangular zero convention or hive normalization is hidden.

If M is not contained in L, (B) forces an empty polytope. If sizes fail, the two total-sum equations force emptiness. When these conditions hold, every coordinate lies between zero and the row sum L_r-M_r. Hence every nonempty Q is compact; its recession cone is zero. There is no unnormalized additive hive constant. If all partitions are empty, Q is the singleton zero array, dimension zero and coefficient one. If some rows/contents vanish, zero coordinates are retained rather than deleted in a parameter-dependent manner.

This is a direct derivation from Gutschwager v3 Section2 pp2-3, not an unproved import of a tableau/polytope theorem. Rassart Prop2.2 pp5-6 supplies an independent primary hive model with fixed rational inequalities (17)-(20); we do not need its bijection as an additional assumption.

## 2. Elementary uniform lattice growth lemma, including thin directions

Let Q_n={x in R^m:Ax<=n u+v} be bounded whenever nonempty, with rational fixed data, and let Q={x:Ax<=u} be a nonempty bounded rational polytope of affine dimension D. Then # (Q_n intersect Z^m)=O(n^D).

At every vertex of Q_n, the active row normals span R^m. Otherwise a nonzero vector orthogonal to all active normals permits sufficiently small perturbations in both signs while retaining every inactive strict inequality, contradicting extremality. Choose m independent active rows I. The vertex is x_I(n)=n v_I+w_I, where v_I=A_I^(-1)u_I and w_I=A_I^(-1)v_Irhs (the subscript rhs denotes the original offset vector restricted to I, not the limiting vertex). There are finitely many such bases. If A v_I<=u fails in a row, the positive leading discrepancy eventually defeats the bounded offset, so this base is infeasible for every sufficiently large n. Take a common threshold over the finitely many offending bases. Every remaining feasible vertex has v_I in Q and w_I in a fixed finite bounded set W.

A compact polyhedron is the convex hull of its vertices: one elementary justification is to start in its minimal face, move along a line in that face to its boundary in both directions, and induct on face dimension to express the point as a convex combination of vertices. Compactness gives both endpoints and terminates this induction. Therefore Q_n is contained in nQ+conv(W) for every sufficiently large n with Q_n nonempty. Empty Q_n contribute zero. This proves bounded thickening with no assumption about equal dimensions of Q_n and Q, and no claim of universal semigroup dominance.

Choose a rational point p of Q and a rational basis of the direction space V=span(Q-Q). Such a basis exists by rational active equations, or by rational vertices and their differences. Extend it to a rational basis of R^m and let U be its inverse coordinate matrix. Then U(V)=R^D times {0}. Since U is rational, U(Z^m) is contained in a fixed grid (1/q)Z^m for some positive integer q. In coordinates U, the last m-D coordinates of Q_n lie within fixed bounded intervals about the corresponding coordinates of nUp. Each such interval meets the grid in O(1) points, uniformly in its center. The first D coordinates lie in intervals of length O(n), since Q and conv(W) are bounded. They meet the grid in O(n) points each. Injectivity of U proves O(n^D). This includes D=0, rational affine spans with no integer point at a particular scale, and changing transverse lattice cosets. Neither integral vertices nor Ehrhart polynomiality is assumed.

## 3. Identify D with the stretched degree without an Ehrhart assumption

Let Q=Q(a). Since f is a nonzero polynomial with nonnegative integer values for all positive integers, it is positive for all sufficiently large n. At some such n*, the lattice model gives x in Q(n*a); then x/n* lies in Q. Q is therefore nonempty and bounded rational. Put D=dim aff Q.

Applying the preceding coordinate-grid bound to nQ gives f(n)=O(n^D). For the reverse exponent choose D+1 affinely independent rational points p_0,...,p_D in Q; rational vertices spanning the affine hull suffice. Choose q>=1 clearing every denominator and put z_i=q p_i in Z^m. For every positive integer t and nonnegative integers m_1,...,m_D with sum m_i<=t, the point

    t z_0 + sum_i m_i (z_i-z_0)

is an integer point of qt Q. These points are distinct because the differences z_i-z_0 are linearly independent. There are binomial(t+D,D) such choices (stars and bars), which is bounded below by a positive constant times t^D (also when D=0). Thus f(qt)>=binomial(t+D,D). A nonzero polynomial nonnegative at all large integers has positive leading coefficient; the upper bound forces d<=D and this subsequence lower bound forces d>=D. Hence d=D. This lower estimate is used only to identify an exponent, and never to infer polynomiality from subsequences or a quasipolynomial.

## 4. Translation, lower growth, and all-integer eventual polynomiality

Choose an integer array y in Q(b), possible because c(b)>0. Every inequality/equality defining the tableau model is additive in its boundary parameters. Therefore x -> x+y maps Q(na) intersect Z^m injectively into Q(na+b) intersect Z^m. This proves P(n)>=f(n) for all positive n, including f(n)=0 cases. It is also exactly the primary addition injection of Gutschwager Lemma3.1, now expressed with fully specified coordinates. In particular P(n)>0 for all sufficiently large n.

The growth lemma gives P(n)=O(n^D)=O(n^d). Gutschwager Lemma5.3 proves existence of an eventual polynomial g, independently of its degree. To spell out the relevant primary specialization: Rassart Definition2.4 and Theorem4.1 give a finite rational polyhedral chamber complex for fixed length k, with polynomial values, including the boundary restrictions used in Gutschwager's argument. For any defining face form ell, ell(na+b)=n ell(a)+ell(b) has eventually fixed sign, or is identically zero. Taking a common threshold for the finitely many forms places the affine ray in one fixed relatively open face for all sufficiently large integers n. The polynomial on that face, evaluated on na+b, is one ordinary polynomial in n. If it is identically on a wall, retain that face; do not replace it by an adjacent interior cone. This also corrects the harmless final-paragraph direction/translation slip in the printed Lemma5.3 explanation. This use of the primary polynomiality theorem, rather than rational-polytope counting alone, is essential: the latter generally gives quasipolynomials.

For all sufficiently large n, g(n)=P(n)>=f(n)>0 and g(n)=O(n^d). Positive leading coefficients now force deg(g)>=d and deg(g)<=d, respectively. This proves the exact asserted degree, on interior and supporting directions alike.

## 5. Degree zero and the 'in particular' sentence

If d=0, f is a positive constant and the argument gives a positive constant g. Choose a positive integer m beyond all thresholds. Since equality holds at m itself, P(n)=g=P(m) for every integer n>=m. There is no claim that the constant equals c(b) or equals one.

For c(a)=1, use the primary Fulton theorem in Knutson-Tao-Woodward, math/0107011v2 Section6.1 p26: multiplicity one in V_mu tensor V_nu for V_lambda remains multiplicity one after multiplying all three highest weights by any positive integer. The tuple convention is output lambda and inputs mu,nu. Therefore f(n)=1; the degree-zero argument applies. Section6.1's statement and proof were read, not its abstract's apparent VN-lambda typo. The full upstream puzzle machinery is trusted as an existing theorem, not re-proved or audited here. No new Fulton result is claimed.

## Dependency and scope audit

The added mathematics is the explicit tableau encoding, the bounded-thickening/lattice estimate and its all-face dimension/degree specialization. Existing primary inputs are the LR tableau definition, finite chamber polynomiality (Rassart), and Fulton multiplicity-one stretching (only for the final sentence). No saturation theorem, integral-hive claim, parametric Ehrhart theorem, finite-generation module assertion, numerical evidence, dominance inference on faces, or formal API is needed. This is a full ordinary proof conditional only on these named established upstream results, in the usual sense of an ordinary source-based proof; it is not the author's formerly conditional model route left unpaid.
