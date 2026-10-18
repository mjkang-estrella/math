# Two full-target attempts and their stopping points

These are author deductions, not an independent review. T023P55 is unchanged and unresolved.

## 1. Prime-series route: the exact missing half-plane

Put alpha=5/6 and Theta_m((a))=(a/|a|)^m for the primary generator. Source angular.tex defines this nonprincipal unitary Hecke character, finite conductor dividing (3), with nonzero infinity type. Its entire continuation is a stipulated source input. The source and Dunn–Radziwill (1.8) give G(pi)^(3m)=(-1)^m Theta_m(pi). Thus the target is exactly A_m(x)=o(x^alpha/log x), where A_m sums Theta_m over the stated primes.

Suppose the target holds. Abel summation gives

    B_m(x):=sum_{N(p)<=x} Theta_m(p) log N(p)
          =A_m(x)log x - integral_2^x A_m(t)/t dt
          =o(x^alpha).

For completeness, given epsilon, bound |A_m(t)|<=epsilon t^alpha/log t beyond a fixed threshold. The endpoint is at most epsilon x^alpha. The integral is O(epsilon x^alpha/log x)+O_epsilon(1), by splitting at sqrt(x); hence the asserted little-oh follows.

Consequently H_m(s)=s integral_1^infinity B_m(t)t^(-s-1)dt is holomorphic for Re(s)>alpha: on each compact set the tail and every s derivative converge uniformly, since powers of log t are integrable against t^(-1-delta). For Re(s)>1 it equals the prime part of -L'/L(s,Theta_m).

The prime-power remainder

    R_m(s)=sum_p sum_{j>=2} Theta_m(p)^j log N(p) / N(p)^(j s)

converges absolutely locally uniformly for Re(s)>1/2. Indeed, for sigma>1/2 the inner absolute sum is bounded by C_sigma log N(p) N(p)^(-2sigma); the sum converges even when extended to all nonzero ideals. The latter follows from the elementary O(x) lattice count of ideals in this class-number-one field. Euler factors at the finite conductor are omitted on both sides; changing a finite set gives a holomorphic term for Re(s)>0.

Thus -L'/L=H_m+R_m on Re(s)>1, and by meromorphic identity on Re(s)>alpha. The right side is holomorphic. Any zero of L there would give a nonzero pole of its logarithmic derivative, a contradiction. Therefore **T023P55 implies L(s,Theta_m) has no zeros with Re(s)>5/6 for every fixed m!=0**.

This establishes necessity, not an equivalence and not zero-freeness itself. In particular, no boundary estimate at Re(s)=5/6 is deduced from a putative open-half-plane zero-free statement. The actual source input is B_m(x)<<_{m,M}x(log x)^(-M), for each fixed M. Its Mellin integral only gives the needed absolute convergence for Re(s)>1, not >5/6. Choosing M depending on x is not permitted; even a fixed arbitrarily large M does not turn x/log^M x into x^(5/6)/log x.

Dunn–Radziwill v3 explicitly identifies this zero-free-strip requirement immediately after Theorem 1.3 (text lines 239–247). Their GRH theorem is conditional, smooth, and is not an unconditional solution. The necessity argument above makes the exact sharp-target interface explicit; the observation itself is credited to them. Finite-order character results cannot be substituted for Theta_m without a new argument: its restriction to the connected archimedean unit circle is nontrivial, whereas every continuous finite-order character on that connected group is trivial. No uninspected finite-order source theorem is imported here.

**Stopping point:** no proof of the required angular zero-free region. The target remains open in this work.

## 2. Cubed dispersion route: a rank-one obstruction at the actual kernel

Source background-type1.tex gives, for coprime squarefree a,b,

    G(ab)=G(a)G(b) conjugate(chi_b(a)).

Cubing removes the residue character because chi_b(a)^3=1. For two distinct primes p,q this yields

    G(pq)^3=G(p)^3 G(q)^3=Theta_1(p)Theta_1(q).

Thus for every nonzero integer m the two-prime kernel G(pq)^(3m) is exactly K_{p,q}=Theta_m(p)Theta_m(q). This uses actual primary primes, not a hypothetical counting set. Take any two finite disjoint primary-prime sets P,Q of sizes L,M. All entries are coprime and the displayed identity applies, including negative m since G(pq) has modulus one. Put u_p=Theta_m(p), v_q=Theta_m(q). Then K=u v^T and

    (K K*)_{p,p'}=M u_p conjugate(u_{p'}),
    sum_{p'!=p}|(K K*)_{p,p'}|^2=(L-1)M^2,
    ||K||_(2->2)=sqrt(LM).

These follow by multiplying the matrices; equality in the operator norm is achieved by the vector conjugate(v)/sqrt(M). Equivalently coefficients a_p=conjugate(u_p), b_q=conjugate(v_q) make the bilinear sum exactly LM. Hence there is no uniform saving from row orthogonality for the cubed kernel, regardless of angular distribution within either prime set.

This is exactly the mechanism that differs from source dual.tex, Lemma character-gram, lines 148–244. There the off-diagonal character chi_a conjugate(chi_b) is primitive and nonprincipal, so its Poisson zero frequency vanishes. After cubing, the residue-character product is principal on coprime inputs even when p!=p'. Off-diagonal is no longer synonymous with nonprincipal. The zero-frequency-removal step cannot be reused.

If one works with more general squarefree factors, the factors mu(a)^m, mu(b)^m from G(n)^3=mu(n)Theta_1(n), when that identity is used, can only supply separate row/column signs. The two-prime calculation already proves the obstruction without needing that composite identity or a uniform claim on nonsquarefree inputs.

This does **not** disprove cancellation for the particular arithmetic coefficients produced by a prime decomposition. Their angular sums might cancel. It proves the unchanged coefficient-uniform dispersion interface is unavailable: cancellation must instead come from those coefficients or a different kernel retaining arithmetic interaction. Estimating those sums by the separate angular prime theorem gives only the logarithmic scale in attempt 1. No new coefficient estimate at exponent 5/6 was obtained.

**Stopping point:** cubing destroys the nonprincipal kernel needed by the proposed adaptation. The full target is neither proved nor refuted.
