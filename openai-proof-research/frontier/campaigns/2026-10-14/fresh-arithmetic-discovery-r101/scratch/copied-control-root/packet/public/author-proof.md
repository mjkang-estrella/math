# DEG-r101: full-scope author proof relative to the stipulated pin

Status: author derivation, awaiting independent mathematical review. This is a research proof note, not a manuscript/release. The frozen statement is `frozen-scope.md` (SHA256 recorded in `notes/freeze-record.json`). No hypothesis has been changed. The strongest comparison below indicates a routine composition of already supplied operations, so this note does not assert a substantial contribution.

## 1. Inputs and the precise use of prior proofs

Write I for the pinned integer paper *A power saving for intersective polynomial differences with an exponent depending only on the degree*, and P for the pinned paper *A Power Saving for Polynomial Differences at Prime Arguments*. Both have date October 5, 2026 and pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Exact URLs, blobs and SHA256 values are in the private source register. These papers and their operative proofs are stipulated inputs in this task.

We use the operations in I's `local.tex` (root normalization), `tuples.tex`, `lifts.tex`, `transfer.tex`, `induction.tex`, and P's `local.tex`, `tuples.tex`, `lifts.tex`, `primes.tex`, `kernel.tex`, `descent.tex`. In particular, the finite weighted-graph/tuple construction is P `prop:tuple-laws` and its proof from `eq:tuple-edge-weight`; the Fourier-lift operations are `prop:signed-holder`, `lem:seminorm`, `lem:large-denominator`, `prop:lift-moments`, `lem:lift-specialization`; the analytic inputs are `prop:prime-progressions` and `prop:prime-minor-arcs`; and the final recurrence is `prop:descent-recurrence`. This proof supplies their compatibility with a different polynomial/prime-test pair. It does not infer prime avoidance from the integer avoidance theorem.

The prime-progression input is the estimate, uniform in a reduced class modulo b,

    sum_{n<=Y, n=a mod b} Lambda'(n)
       = Y/phi(b) + O(Y^(31/32) log^2(2bY)),

where Lambda'(n)=log(n) for primes and zero otherwise. P proves this from its stipulated zero-free input; we use that proof operation, without an upstream truth audit. P's prime polynomial-sum input supplies a number c_m(k,rho)>0: a degree-k real phase with leading coefficient b_k has prime sum O(Y^(1-c_m)), uniformly over subintervals of [1,Y] and over all lower coefficients, if (k!)^2 b_k has a rational approximation a/q of error at most q^-2 with Y^rho<=q<=Y^(k-rho). These are stronger inputs than the classical logarithmic estimates; the present claim is explicitly relative to the supplied source context.

For clarity on novelty, Lucier (2006), Section 8, especially Lemmas 24–28, already handles auxiliary polynomial content and its divisibility. Rice (2013, corrected arXiv v5), Section 2 and Proposition 4, carries the unit-root affine prime progression through descent; Lemma 9 and Appendix A separate p dividing the affine slope from p not dividing it. Rice (2019, arXiv v5), Sections 2.5 and 4, supplies derivative sieving and prime-power regular-lift cancellation. Those are actual body comparisons, not claims based on their abstracts.

## 2. The content issue, and why it is not the bridge

For f,g in Z[x], f(Dx-i)=lambda(D)g(x) immediately implies

    cont(f) | lambda(D) cont(g).

Indeed every coefficient of f(Dx-i) is an integer combination of coefficients of f, and the content of lambda(D)g is lambda(D)cont(g). Here cont includes the constant coefficient. The same argument for the ideal of nonconstant coefficients works with Lucier's convention, since the constant term of f contributes only to the constant term after substitution. Thus the divisibility left open in r100 was already paid. Dividing each auxiliary polynomial by its individual content would introduce a variable progression factor. We do not use that renormalization.

Instead perform I's root normalization once, before the family is formed, and retain the original prime test as an affine function.

## 3. Normalize the polynomial while retaining primality

Fix h of the frozen scope, with leading coefficient a>0. Choose for every p a root z_p in Z_p^*. Let its multiplicity be m_p, 1<=m_p<=k, and write

    h(z_p+X) = sum_{j=m_p}^k b_{j,p} X^j,
    t_p = v_p(b_{m_p,p}).

Only finitely many t_p are positive. This is the finite-exception assertion in I's normalization proof: factor h into distinct primitive irreducible factors with multiplicities, exclude primes dividing its scalar, factor leading coefficients, relevant discriminants and pairwise resultants, and the first coefficient at any root is a unit at every remaining prime. This supplies finiteness, not a degree-only bound on that exceptional set.

Set S={p:t_p>0}, u_p=t_p+1, and

    D0 = product_{p in S} p^u_p,
    M  = product_{p in S} p^(u_p m_p+t_p).

Choose r in (-D0,0] with r=z_p mod p^u_p for p in S, and define

    g(x)=h(r+D0 x)/M,       w_p=(z_p-r)/D0.

For p not dividing D0, w_p is integral because D0 is a p-adic unit; for p dividing D0, integrality follows from the choice of r. In the expansion of g at w_p, the coefficient in degree j is b_{j,p}D0^j/M. Its valuation at p in S is

    v_p(b_{j,p}) + u_p(j-m_p) - t_p.

It is zero at j=m_p, positive for j>m_p, and the lower coefficients vanish. At p outside S the first coefficient is again a unit and all coefficients are integral. Translation by w_p preserves integrality in Z_p[x]. Consequently g belongs to Z[x], has positive leading coefficient a_g=aD0^k/M, and its first nonzero Taylor coefficient at every chosen root w_p is a unit. In particular g mod p is nonconstant for every p. Notice that w_p need not be a unit. We do not claim g is prime-intersective and do not apply P's headline theorem to g at prime arguments.

Let lambda be completely multiplicative with lambda(p)=p^m_p. For every l>=1 take the coherent representative s_l in (-l,0] of w_p modulo p^v_p(l). Define the pair

    F_l(x)=g(s_l+l x)/lambda(l),
    T_l(x)=r+D0(s_l+l x)=R_l+W_l x,
    R_l=r+D0 s_l,             W_l=D0 l.                     (1)

The auxiliary-polynomial calculation of I gives F_l in Z[x], degree k, leading coefficient a_l=a_g l^k/lambda(l), and every coefficient O_g(a_l), uniformly in l. A direct check at the root (w_p-s_l)/l shows that its first nonzero Taylor coefficient is still a p-adic unit: division by lambda(l) cancels exactly m_p v_p(l). Thus every F_l mod p is nonconstant, uniformly for all l,p.

Furthermore gcd(R_l,W_l)=1. At p dividing D0, R_l is congruent to z_p modulo p^(v_p(D0)+v_p(l)); at p dividing l but not D0 it is congruent to z_p modulo p^v_p(l). All these z_p are units. Also -W_l<R_l<=0, so T_l(m)>0 for every integer m>=1. The case D0=1,r=0 presents no exception: gcd(0,1)=1.

Coherence yields s_{lD}=s_l-il with 0<=i<D. We then have BOTH identities

    F_l(Dx-i)=lambda(D) F_{lD}(x),
    T_l(Dx-i)=T_{lD}(x).                                    (2)

Write mathcal D_l={F_l(m):m>=1, T_l(m) prime}. If A avoids its nonzero values and a+lambda(D)B is a subset of A, then B avoids the nonzero values of mathcal D_{lD}: a forbidden difference in B, multiplied by lambda(D), would be F_l(Dm-i), with Dm-i>=1 and the same positive prime. Zero is preserved exactly by the positive scalar lambda(D). This proves the avoidance interface needed by every subsequent descent.

## 4. Degree-only local parameters with the affine unit condition

An argument x modulo p is allowed if p does not divide T_l(x). Since gcd(R_l,W_l)=1, there are either p or p-1 allowed residues. At a large prime it is allowed regular if also F_l'(x) is nonzero modulo p. For p>k, F_l mod p is nonconstant and its derivative is not the zero polynomial. Removing its at most k-1 derivative roots and the at most one excluded prime residue leaves at least p-k arguments.

Use the local-sum operation in P `lem:local-sums`, now with F_l and this allowed set. The proof uses polynomial degree, nonconstancy modulo p, and removal of at most k residues, so its threshold P1 may be chosen as a function of k alone. Enlarge it above 2k. The exponents can be those of P,

    delta=1/(100 k 2^k),       gamma=delta/10.

The normalized local Fourier bounds used below are at most p^(-4 delta), and regular prime-power sums have the same lifting behavior as P. No original coefficient exception is inserted into P1.

Here is an explicit bound for the small-prime derivative step, including the allowed condition. Put

    T(k,p)=max_{1<=j<=k} v_p(j),
    B(k,p)=(k-1) floor(log_p(kp)),
    S_p=T(k,p)+B(k,p).

Some nonconstant coefficient of F_l is a p-adic unit, so some coefficient of F_l' has valuation at most T(k,p). There are at least k distinct allowed integers in [1,kp]; choose k of them. Each Lagrange interpolation denominator for a polynomial of degree at most k-1 is a product of k-1 nonzero differences of absolute value less than kp, so has valuation at most B(k,p). If F_l' at all chosen integers were divisible by p^(S_p+1), every coefficient of F_l' would be divisible by p^(T(k,p)+1), a contradiction. Thus one allowed x has s=v_p(F_l'(x))<=S_p.

Set E_p=2S_p+1 for p<P1, and E_p=1 otherwise. In the small-prime argument class x+p^(E_p-s)Z_p, Taylor expansion has a unit linear term after division by p^E_p, and all higher terms are divisible by p. Indeed E_p>=2s+1. The induced map onto the value class F_l(x)+p^E_p Z_p is a measure-preserving bijection at each further finite level, by successive digit lifting. The whole argument class remains allowed since E_p-s>=1. This is precisely P `lem:local-lifting`, now with degree-only E_p. For p>=P1 the regular class has s=0 and E_p=1.

Choose a degree-only integer L>max(2,1/(2 delta)) divisible by every p^E_p with p<P1. At each small prime an admissible value repeated L times sums to zero. At every larger prime the Fourier estimate supplies an admissible L-cycle, as in P `lem:admissible-cycle`. Choose t>=1 with (t+1)delta/2>5 and put

    d=(L!)^(2t+1).

For p>=P1 define the edge weight

    W_{l,p}(y)=(1/k) #{x mod p : F_l(x)=y, x allowed regular}.

It satisfies 0<=W<=1, mean at least 1/(2k), and nontrivial normalized Fourier coefficients at most p^(-4delta). These are all the numeric inputs to the weighted-graph estimates and tuple construction in P, whose proofs are given in full there. Its constants depend only on k,L,t. Therefore its final threshold P>P1 can be chosen depending only on k. In particular no h-dependent discriminant threshold survives in the tuple size.

The affine covariance needed by that construction holds exactly. When p does not divide D, the bijection x->Dx-i preserves allowed arguments by the second identity in (2), preserves regularity by differentiating the first, and scales values by lambda(D). Thus the pushed-forward tuple measures and their exceptional submeasures at l equal those at lD under the label transformation z->lambda(D)^(-1)(z-a'). This includes primes dividing D0; no special loss occurs there.

We consequently have reflection-positive tuple probabilities mu_{l,p}, exceptional submeasures epsilon_{l,p} of mass eta_{l,p}<=p^-4, uniform one-coordinate marginals, admissible cycle increments off the exceptional measure, and conditional mixing at most p^-gamma, exactly as in P `prop:tuple-laws`. Increase P, still depending only on k, to make the exceptional budget in Section 6 at most 1/4. Put

    M0=product_{p<P} p^E_p,       rho_*=M0^(1-L)>0.            (3)

All quantities in (3), as well as d, depend only on k. The repeated-cycle/CRT argument gives good residue assignments of proportion rho_l>=rho_* for every l.

## 5. Prime weights and the kernel: checking the changed slope

Retain the tuple Fourier lifts and their moment/specialization proofs from P. They use only the just verified tuple interfaces and lambda, so need no alteration. The analytic point requiring alteration is the prime weight. For a period b the number of allowed argument classes is

    n_b=b product_{p|b, p not dividing W_l}(1-1/p)
       =phi(W_l b)/phi(W_l).                                (4)

It is W_l=D0 l here, not l. Uniform averages over these classes factor over coprime prime powers and are consistent on refinement.

For an admissible target residue r' modulo D=M0 product_{p in B}p, the local lifting class at p has argument period p^(E_p-s_p). Combine them to period d_{r'} dividing D, and set rho_D=n_{d_{r'}} times that class's indicator. Its unit mean is one and its supremum and Fourier l1 norm are at most D. For a prime p not dividing D, let pi_p be the distribution of a directed cycle increment under the normalized good tuple measure. Choose an allowed regular preimage x_y for every y in its support and set psi_p(x_y)=n_p pi_p(y), zero at other classes. This is well-defined since distinct values have distinct selected preimages. It has unit mean one and pushes forward to pi_p. Set B_p=psi_p-1 and B_u=product_{p|u}B_p for squarefree u coprime to D. Then |B_u|<=u, its period is u, and its Fourier l1 norm is at most u^2. These are exactly the inputs in P `kernel.tex`.

Choose the analytic parameters

    eta=1/(10000k),  c_m=c_m(k,eta/4),
    nu=min(eta,c_m/k)/10,
    beta=zeta=nu/100,
    tau=beta gamma/[1000k(d+1)],   sigma=gamma tau/4.          (5)

They now depend only on k. Take l<=N^zeta, Q=N^beta, H=N^(beta/2), D<=N^beta. Uniform coefficient bounds give a fixed x_*=x_*(h) after which F_l,F_l' are positive and

    F_l(x) asymp_h a_l x^k,  F_l'(x) asymp_h a_l x^(k-1),
    |F_l''(x)| <<_h a_l x^(k-2).

With U=(N/a_l)^(1/k) let F_l(X)=N, so X asymp_h U and U>>_h N^(1/k-zeta). Define the signed kernel

    k1(n)=sum_{x_*<m<=X} 1_{n=F_l(m)} [F_l'(m)/N]
           [phi(W_l)/W_l] Lambda'(T_l(m)) rho_D(m)
           sum_{u<=H, squarefree, (u,D)=1} B_u(m).           (6)

Every nonzero term is an actual positive member of mathcal D_l. Signed weights cause no support issue. For the prime range take Y=C_h W_l U, large enough to cover T_l(X). Its crucial relations are

    Y^k asymp_h (M/a) N lambda(l),
    Y>>_h N^(1/k),  Y<<_h N^(1/k+zeta),  Y<=N               (7)

at sufficiently large N depending on h. Fixed D0 and M do not enter any exponent in (5).

For completeness, here is the minor-arc check where a covert coefficient-dependent exponent would otherwise be possible. Under n=T_l(m), the phase alpha F_l(m)+y'm has degree-k leading coefficient

    b_k=alpha a/[M lambda(l)].                              (8)

The restriction n=R_l mod W_l is the average of W_l additive characters; its Fourier l1 norm is one. All twists alter only lower coefficients because k>=2. Dirichlet approximation to (k!)^2 b_k at Q0=floor(Y^k N^(-eta/2)) produces a'/q, q<=Q0, with error <=q^-2. Equation (7) places alpha within O_h(N^(-1+eta/2)) of a rational with denominator at most (k!)^2 a q: multiplication of its numerator by M lambda(l) introduces no additional denominator. Off the major arcs of radius 3N^(-1+eta) and denominator <=N^eta, this implies q>=N^eta/C_h. Enlarging the h-dependent threshold gives

    Y^(eta/4)<=q<=Y^(k-eta/4).

P's prime-minor-arcs operation therefore gives O_h(Y^(1-c_m)), uniformly in the interval and twists. From (7) this is at most O_h(U l N^(-c_m/k)), hence O_h(U N^-nu). Partial summation against F_l'/N, whose supremum and total variation are O_h(U^-1), and the periodic Fourier expansions in (6), give

    |S1(alpha)| <<_h D H^3 N^-nu.

The model kernel of P is

    k0(n)=(D/N)1_{1<=n<=N}1_{n=r' mod D}
             sum_{xi in Xi} Gamma(xi)e(-xi n),

where Xi comprises squarefree denominators <=H coprime to D, and Gamma is the product of the edge multipliers. Its minor-arc bound is O(DH^2 N^-eta). The corresponding exponents are 5beta/2-nu and 2beta-eta, both strictly less than -beta gamma/4.

On a major arc alpha=alpha0+y, q(alpha0)<=N^eta, |y|<=3N^(-1+eta), the class m=c mod b corresponds to n=R_l+W_l c mod W_l b. It is reduced exactly when (T_l(c),b)=1, by gcd(R_l,W_l)=1. The prime-progression main term multiplied by phi(W_l)/W_l is

    [phi(W_l)/W_l] [W_l length(I)/phi(W_l b)]
       = length(I)/n_b.

Thus (4) gives precisely the unit mean required for the local Fourier coefficient. Nonreduced classes contribute at most O(log(W_l bY)) from the finitely many possible prime divisors. With b=lcm(q,d_{r'},u), the weighted progression error is bounded, as in P `eq:weighted-prime-progression`, by O_h(qD^2u^2 Y^(31/32)log^2(2W_l bY)). Relation (7) gives

    Y^(31/32)/U <<_h l N^(-1/(32k)).

Summing u<=H and partial summation reproduce the major-arc error exponents

    2eta+4beta+zeta-1/(32k)+o(1),
    2beta+k zeta-1,     2beta+eta-1.

All are less than -beta gamma/4 by (5), k>=2. Constants involving D0,M,a or g are absorbed only by the prefactor and N_h.

It remains to identify the rational coefficient, not just bound the analytic error. At p dividing D, the chosen argument class pushes forward uniformly over all higher lifts of r'. Its local coefficient is the fixed phase when the conductor divides p^E_p and zero at larger conductors. At p not dividing D, psi_p pushes forward to pi_p at conductor p and has zero primitive coefficients at higher p-powers, because its chosen arguments are regular and uniform lifting applies. All these facts hold with the modified unit means (4). Products of 1+B_p therefore yield exactly Gamma(alpha1) times the D-supported phase whenever the non-D part alpha1 has squarefree denominator <=H; otherwise the omitted tail is O(H^-gamma/2), using |Gamma(xi)|<=q(xi)^-gamma and the same local-sum bounds. This is the coefficient comparison in P `eq:kernel-local-realization`; its proof uses precisely the verified unit means, lifting, and local Fourier bounds. No prime test has been dropped.

Consequently P's `lem:kernel-comparison` holds for (1):

    sup_alpha |S0(alpha)-S1(alpha)| <<_h H^-gamma/2.          (9)

Plancherel and the actual forbidden support of (6) now give P `prop:pair-cancellation` for ordered supports avoiding mathcal D_l. This completes the analytic interface needed for the descent.

## 6. The recurrence and the degree-only exponent

To specify the source quantity: let mathcal P_N be the primes P<=p<=Q, X_mathcalP=product F_p, and use normalized Fourier coefficients of f on [N]. Its lift is the sum of these coefficients times the CRT characters on X_mathcalP over squarefree denominators <=Q supported on mathcalP. For a real lift G set

    Z_l(G)=integral product_{v in V}G(z_v) d(tensor_{p in mathcalP_N}mu_{l,p}).

Let Y_l(N,A)=Z_l(lift(1_A)), and let mathcal Y_l(N) be its maximum over A subset [N] avoiding nonzero mathcal D_l. The reflection/seminorm and moment operations in P `lifts.tex` give

    (|A|/N)^d <= Y_l(N,A),       0<=mathcal Y_l(N)<<_k,epsilon N^epsilon  (10)

for every epsilon>0 and EVERY l>=1. In particular the subpower bound is not restricted to l<=N^zeta.

Here are the dependencies of the descent, to avoid treating its printed h-dependent theorem as automatically uniform. Residue specialization and shorter intervals use covariance (2), the support rad(lambda(D))=rad(D), and D<=lambda(D)<=D^k. The forbidden-set inheritance was proved in Section 3. Good assignments modulo M0 occur with probability rho_l>=rho_* by Section 4. Cancellation on good assignments uses (9); its lift cutoffs and moment estimates depend only on d,gamma and (5). The exceptional mass satisfies eta_{l,p}<=p^-4, so increasing P by a degree-only amount gives

    sum_{nonempty finite B} q_B eta_{l,B} <= 1/4,
    q_B=product_{p in B}p, eta_{l,B}=product_{p in B}eta_{l,p}. (11)

The proof of P `prop:descent-recurrence` thus applies verbatim after the verified replacements and gives, for l<=N^zeta and N sufficiently large depending on h,

    mathcal Y_l(N) <= C1(h)N^-sigma + (1+u_N) [
       (1-rho_l)mathcal Y_{lM0}(n_empty)
       +rho_l sum_{B nonempty, q_B<=N^tau}
                     eta_{l,B} mathcal Y_{lD_B}(n_B)],       (12)

where D_B=M0 q_B, n_B=ceil(N/lambda(D_B)), and

    u_N=(1+M0^k N^(k tau-1))^d-1=o(1).

For large enough N all child scales obey N^(1/2)<=n_B<N. This is the exact recurrence of the source: C1 and its starting threshold may depend on h; its structural parameters now do not. No unproved normalized-family recurrence is being assumed: the family, covariance, tuple, kernel and avoidance interfaces used to derive it have all been checked above.

For an explicit degree-only choice put K0=k+2/zeta and

    a0=(1/2)min{sigma, 1/K0,
                   -log(1-3rho_*/4)/(K0 log M0)},
    b0=2a0/zeta,   s0=ka0+b0,   c_k=a0/d.                  (13)

Then a0>0, a0<sigma, s0<=1, and theta0=M0^s0(1-3rho_*/4)<1. Prove simultaneously for all integers l>=1, by induction on N,

    mathcal Y_l(N)<=C0(h) l^b0 N^-a0.                       (14)

If l>N^zeta, the right-hand factor l^b0 N^-a0>=N^a0, so (10), with epsilon=a0, proves (14) after choosing C0. This also covers every l for the bounded initial scales. Otherwise use (12), whose child scales are smaller. The induction hypothesis, including children outside their analytic range, gives

    mathcal Y_{lD_B}(n_B)
       <= C0 l^b0 N^-a0 D_B^(ka0+b0).

Since q_B^s0<=q_B, (11) bounds the bracket in (12), after division by C0 l^b0 N^-a0, by

    M0^s0[(1-rho_l)+rho_l/4]<=theta0<1.

Choose the h-dependent threshold large enough that

    C1(h)N^(a0-sigma)+(1+u_N)theta0<=1.

Then choose C0>=1 to cover the initial scales using (10). This proves (14) and hence, at l=1,

    |B|<=C0(h)^(1/d) n^(1-c_k)

for every B subset [n] avoiding nonzero mathcal D_1 (enlarging C0 handles all n>=1). This proves the full normalized-family bound with exponent (13) depending ONLY on k.

Finally s_1=0, so F_1=g and T_1(x)=r+D0 x. Partition the original A by its residue class modulo M. In each class write a+M B subset A with B in an interval of length at most ceil(N/M), translated to [ceil(N/M)]. If B had difference F_1(m) with T_1(m) prime, the original set would have difference

    M F_1(m)=h(T_1(m)),

contrary to the original avoidance. Applying the normalized bound in every class, for N>=M,

    |A|<=M C0(h)^(1/d) ceil(N/M)^(1-c_k)
       <=2^(1-c_k) M^c_k C0(h)^(1/d) N^(1-c_k).

This is exactly the frozen DEG claim, for all prime-intersective degree-k polynomials with positive leading coefficient. The potentially enormous M is permitted in C_h and N_h, and never changes c_k. QED (author proof relative to the stipulated operations).

## 7. What this does and does not contribute

The formal content divisibility is elementary and explicitly present in Lucier's auxiliary theory. The useful integration is to normalize once and transport the affine prime test alongside the polynomial, replacing every occurrence of the slope in the unit means and the prime weight. The proof above tracks that replacement through the local parameters, covariance, kernel and induction, including the primes dividing the normalization modulus.

This removes the specific r100 feasibility obstruction in the stated source context; it does not turn the provider's r100 failure into a mathematical result. It also does not claim a new prime theorem from the integer headline theorem. The stronger available input is the COMBINATION of I's operative normalization and P's affine-prime proof machinery, reinforced by the already classical Lucier/Rice interfaces. The author assessment is that this is a routine source composition. A separate reviewer owns correctness and contribution judgments. There is no asserted remaining author-proof gap in DEG, but there is also no identified nonroutine operation warranting a substantial-result nomination. The separate phase-mask diagnostic records a tested distinct direction and its obstruction.
