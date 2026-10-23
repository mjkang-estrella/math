# Author proof of the frozen compact-factorization target

This proves the exact statement in FROZEN-STATEMENT.md (SHA256 fbd2600bdc050aac6e4ab130c3d4a35f88db4fa2af26b5e2b163ee922d760433). It is discovery-stage author work, not an independent correctness review, contribution verdict, formalization, manuscript, or release.

## 1. Dependencies and normalization

All spaces and linear maps in the proof are real. All finite probability spaces carry uniform probability measure; ell2 direct sums carry the sum-of-squares norm. We use the quotient-duality and finite-level lift operation proved in Source326, preliminaries.tex, equation eq:quotient-lift, and approximation.tex, proof of lem:compact-domain. The proof below reproduces the precise finite-level operation to expose its inputs and constants. No truth audit of the stipulated source is being performed.

The other ingredients are elementary Banach-space facts: a countable ell2 sum of finite-dimensional spaces is separable and reflexive; a quotient of a reflexive space by a closed subspace is reflexive; a uniformly small tail with finite sets of possible coordinate values is relatively compact in an ell2 sum; and conditional expectation contracts the L2 norm. These facts do not require AP. They are also mechanisms underlying classical compact factorization; see the primary comparison at the end.

Fix r>=2, D>=1, X,Y,T,E as in the frozen statement. For m>=1 put

    Delta_m = D m^(1/2-1/r).

The assumed cotype-r estimate on X* and the finite-dimensional inequality ||a||_2 <= m^(1/2-1/r)||a||_r give c_m(X*) <= Delta_m, where c_m is the source's fixed-length ell2 cotype constant.

If X={0}, take G={0} and all maps zero. All conclusions follow, with C_s({0})=0. In the sequel the construction also permits E={0}, T=0, or some initial finite-dimensional spaces equal to zero.

If T is nonzero, let K be the norm closure of {Ty/||T||: ||y||<=1}. This is compact, lies in B_X, and contains zero. If T=0, put K={0}. For each integer l>=0 choose a finite set N_l subset K such that every x in K is within

    eta_l = 2^(-2l-4)

of some element of N_l. Such finite nets exist by compactness. No nets of an infinite-dimensional unit ball are taken.

## 2. Finite-level lifts, simultaneously at finitely many lengths

For any finite-dimensional F subset X and integer m>=1 there is a finite-dimensional F' containing F such that each z=(z_i) in ell2^m(F) has a function h:{-1,1}^m -> F' with

    E_epsilon epsilon_i h(epsilon) = z_i,
    ||h||_(L2(F')) <= 3 Delta_m ||z||_(ell2^m(F)).                 (2.1)

Here is the source operation with constants visible. On the whole space X, define

    V_m:L2({-1,1}^m;X) -> ell2^m(X),
    V_m h = (E_epsilon epsilon_i h(epsilon))_i.

It is surjective: z -> sum_i epsilon_i z_i is a bounded right inverse. Its adjoint sends (x_i*) to sum_i epsilon_i x_i*. Thus c_m(X*)<=Delta_m gives

    ||V_m*(x_i*)||_L2 >= Delta_m^(-1) ||(x_i*)||_ell2.

Quotient duality implies that a unit tuple in ell2^m(X) has a lift of norm strictly less than 2 Delta_m. Choose an alpha-net of the unit sphere of ell2^m(F), with

    0 < alpha <= min(1/2, Delta_m/sqrt(m)),

and one such lift for every net point. Let F' contain F and all values of these finitely many functions. For a unit tuple z choose a net point v and add sum_i epsilon_i(z_i-v_i) to its chosen lift. This corrects all moments exactly and costs at most

    sqrt(m)||z-v||_ell2 <= Delta_m

in L2 norm. Scaling proves (2.1). If F={0}, the zero lift suffices. For finitely many values of m one takes the span of all the resulting finite-dimensional enlargements. Enlarging the range does not change any norms, since these are subspaces of X.

Set

    M_l = 2^(2^l),          l=0,1,2,... .

Construct nested finite-dimensional subspaces E_l of X inductively as follows. Let E_0=span(E union N_0). Having chosen E_l, choose E_(l+1) to contain E_l, N_(l+1), and the values of the lifts just constructed for every m=1,...,M_l on ell2^m(E_l). This uses finitely many finite nets and finitely many lift values, so their span together with E_l is finite-dimensional. Consequently, for every l and every m<=M_l, (2.1) holds with F=E_l and F'=E_(l+1), using the same Delta_m. No assertion of a linear choice of lifts is made or needed.

## 3. The compact quotient and the prescribed finite-dimensional subspace

Let

    H = (direct sum_(l>=0) E_l)_ell2,
    j:H -> X,             j(z)=sum_(l>=0) 2^(-l) z_l.

The series converges absolutely by Cauchy–Schwarz and

    ||j|| <= (sum_(l>=0) 4^(-l))^(1/2) = sqrt(4/3) < 2.        (3.1)

Its truncation after coordinate L has finite rank and the tail operator has norm at most (sum_(l>L)4^(-l))^(1/2), which tends to zero. Therefore j is compact.

Let G=H/ker(j), Q:H->G the quotient map, and define J:G->X by JQ=j. The kernel is closed. Thus G is a Banach space; J is well-defined, injective, and has norm at most sqrt(4/3). Since H is a countable ell2 sum of finite-dimensional spaces, H and its quotient G are separable and reflexive. Reflexivity here comes from the actual construction, not from a type assertion.

Every g in B_G has a representative z in 2 B_H. Hence J(B_G) is contained in j(2B_H), a relatively compact set, so J is compact. We have not asserted that j's finite-rank truncations descend to G; generally they need not.

For x in E define i(x)=Q(x,0,0,...). Since E subset E_0, this is a linear contraction and Ji(x)=x. If E is nonzero, it follows also that i is injective. No complementability of E is required.

## 4. Moving all short coordinates to one permissible level

This is the compatibility step that is absent from a separate application of the source lemma at each tuple length.

For an integer L>=0 define P_L:H->H by

    (P_L z)_l = 0                                     if l<L,
    (P_L z)_L = sum_(h=0)^L 2^(L-h) z_h,
    (P_L z)_l = z_l                                   if l>L.

Nesting E_h subset E_L ensures that this is well-defined. By Cauchy–Schwarz,

    ||P_L|| <= beta_L,
    beta_L = (sum_(h=0)^L 4^(L-h))^(1/2)
           = ((4^(L+1)-1)/3)^(1/2) <= 2^(L+1).         (4.1)

The untouched tail does not enlarge this bound because beta_L>=1. The weights were chosen so that jP_L=j exactly. Since J is injective and JQ=j, it follows that

    QP_L=Q.                                            (4.2)

Also let R:H->H be the weighted right shift

    R(z_0,z_1,...)=(0,2z_0,2z_1,...).

It is bounded with norm at most 2, is well-defined by nesting, and satisfies jR=j and hence QR=Q.

Fix m>=1, and let L=L(m) be the least l>=0 with m<=M_l. Then m<=M_l for every l>=L. Moreover,

    2^L <= 2(1+log_2(m)).                               (4.3)

For m=1,2 this is immediate since L=0. If m>2 and L>=1, minimality gives m>2^(2^(L-1)), so 2^L<2log_2(m).

Given g_1,...,g_m in G choose z^i in H with Qz^i=g_i and ||z^i||<=2||g_i||, using z^i=0 if g_i=0. Put u^i=P_L z^i. These representatives have no coordinates below L. At each l>=L apply (2.1) to the tuple (u_l^i)_(i=1)^m, obtaining h_l with its values in E_(l+1). Put

    v(epsilon)_0=0,
    v(epsilon)_(l+1)=2h_l(epsilon)  for l>=L,
    v(epsilon)_(l+1)=0             for l<L.

The square-sum estimate is

    ||v||_L2(H)^2
      = 4 sum_(l>=L) ||h_l||_L2(X)^2
      <= 36 Delta_m^2 sum_i ||P_L z^i||_H^2
      <= 144 Delta_m^2 beta_L^2 sum_i ||g_i||_G^2.       (4.4)

Every atom of the finite sign cube has positive measure, so (4.4) proves v(epsilon) belongs to H for every epsilon. Coordinatewise finite-sum expectation is continuous in H. The i-th moment of v is Ru^i. Therefore

    E_epsilon epsilon_i Qv(epsilon)
      = QR P_L z^i = QP_L z^i = Qz^i = g_i.             (4.5)

In particular the shift loss is controlled uniformly by beta_L, not by dimensions of E_l, chosen representatives, or a bound on approximating operators.

For theta_1,...,theta_m in G*, (4.5), Cauchy–Schwarz, and (4.4) give

    |sum_i theta_i(g_i)|
      <= 12 Delta_m beta_L (sum_i||g_i||^2)^(1/2)
           (E_epsilon||sum_i epsilon_i theta_i||^2)^(1/2).

Taking the supremum over the ell2 unit ball of tuples (g_i) yields

    c_m(G*) <= 12 Delta_m beta_L
             <= 48 D (1+log_2(m)) m^(1/2-1/r),         (4.6)

by (4.1) and (4.3). This is one estimate for one fixed G, valid for every m. It does not rely on passing cotype through a quotient.

## 5. From all fixed-length bounds to every cotype exponent above r

Let theta_1,...,theta_n be a finite tuple in G*, reordered so a_i=||theta_i|| is nonincreasing. Write

    A = (E_epsilon||sum_(i=1)^n epsilon_i theta_i||^2)^(1/2).

For k<=n, the Rademacher norm of the first k terms is at most A: condition on the first k signs and average the remaining independent signs, then apply Jensen. Applying (4.6) to that first k-tuple gives

    sqrt(k) a_k
      <= (sum_(i=1)^k a_i^2)^(1/2)
      <= 48 D (1+log_2(k)) k^(1/2-1/r) A.

Thus a_k <= 48 D (1+log_2(k)) k^(-1/r) A. For every s>r,

    (sum_(k=1)^n a_k^s)^(1/s)
      <= 48 D (sum_(k=1)^infinity
                    (1+log_2(k))^s k^(-s/r))^(1/s) A
      = 48 D H(r,s) A.                                (5.1)

The displayed series converges because s/r>1 and any fixed power of log(k) is dominated eventually by k^epsilon for every epsilon>0. This proves the exact simultaneous cotype conclusion. Neither the spaces E_l nor G were chosen using s. No assertion is made at s=r: the estimate used in (5.1) does not give a convergent series there.

## 6. Compact lifting of the entire compact operator

For each x in K choose v_l(x) in N_l with ||v_l(x)-x||<=eta_l. Define a representative in H by

    z(x)_0 = v_0(x),
    z(x)_l = 2^l(v_l(x)-v_(l-1)(x)),          l>=1.

The l-th coordinate lies in E_l. Since K subset B_X,

    ||z(x)_0||<=1,
    ||z(x)_l|| <= 2^l(eta_l+eta_(l-1))
                 = (5/16) 2^(-l),           l>=1.

Therefore

    ||z(x)||_H^2 <= 1 + (25/256) sum_(l>=1)4^(-l)
                 = 793/768 < 4.                       (6.1)

The weighted series telescopes: j(z(x))=lim_l v_l(x)=x. For each fixed l there are only finitely many possible values of z(x)_l, while the square-sum tails tend to zero uniformly in x. Hence Z_K={z(x):x in K} is relatively compact in H. Its closure is compact. Applying Q gives a relatively compact family of lifts in G.

Injectivity of J is crucial. It implies that Qz(x) is independent of all net choices, since it is the unique g with Jg=x. Moreover the set {Qz(x):x in K} is closed: if Qz(x_j) converges to g, continuity of J gives x_j->Jg in the closed set K; the uniquely defined lift of Jg must be g. Consequently

    K_G := {J^(-1)x : x in K}

is a compact subset of G, with sup_(g in K_G)||g||<=sqrt(793/768)<2.

If T=0 define U=0. Otherwise range(T) is contained in range(J), since every Ty is a scalar multiple of an element of K. Define U=J^(-1)T. This is linear by injectivity of J and linearity of its range. For ||y||<=1,

    Uy in ||T|| K_G,
    ||Uy|| <= sqrt(793/768)||T|| < 2||T||.

Thus U is bounded and compact. The identity JU=T holds by construction. Equations (3.1), (5.1), and the definition of i give every assertion of the frozen statement. This completes the author proof.

## 7. What the proof does and does not add to the paid mechanisms

Source326's compact-domain proof already pays for the finite net lifts, the weighted ell2 quotient, the identity QR=Q, and the use of compact maps without uniform AP bounds. Figiel 1973, Proposition 3.1 and Corollary 3.3, already pays for compact factorization through a separable reflexive space; its Sections 5–6 provide the actual universal-space factorization construction. None of those operations is claimed here as new.

The proposed additional construction is the single hierarchy E_l handling every length up to 2^(2^l), combined with P_L. P_L concentrates all levels too early for a chosen tuple length into one admissible level, preserves j exactly, and has loss at most logarithmic in tuple length. This gives global dual cotype for the very same quotient G. The compact net telescope then puts the entire compact image, not just individual finite-dimensional spaces, into that quotient with relatively compact lifts. These statements do not follow by choosing unrelated G_m and taking their direct sum: such a sum supplies neither a fixed quotient with all moments nor unique compact lifts.

This identifies a concrete operation for contribution review; it does not determine its substantiality or novelty. Figiel's universal C_p construction contains all finite-dimensional geometries and does not itself assert the dual-cotype estimates above. Source326 states only one fixed-length estimate for its chosen compact domain. No claim of absence from the wider literature follows from these observations or from access failures. The exact boundary s=r and any AP/K-convexity statement about G remain outside the frozen scope.

## 8. Late primary comparator

After this proof and the exact statement were written, the complete original Jarchow–Matter 1988 paper was visually read. Its actual interpolation construction (10), combined with (12)(a), gives two compact factors for T* with cotype s>r on one factor. DERIVATIONS.md carries that compatible construction and its omitted Holder step explicitly. These are operator-cotype estimates, not cotype of the intermediate identity; the construction also depends on s. The frozen theorem and proof above are unchanged. This is a disclosed late comparison, not a priority certificate or contribution decision.
