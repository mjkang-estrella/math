# Ordinary resolution of Banić–Elezović Conjecture 7.7

Uncredited, pending independent review, current-prior clearance and root's substantive-credit decision. This is an ordinary source-dependent proof, not a formal certificate or manuscript.

Primary body: https://arxiv.org/pdf/2610.17046, v1, submitted 12 October 2026 16:17:43 UTC. Conjecture 7.7, printed p60; Definition 7.4, Eq(7.3), printed p57. Frozen PDF and extracted text hashes are in access.json/freeze.json. The source's already proved Lemmas 6.6–6.8 and 7.3 are dependencies, not new results here.

For every integer l≥0 let (X1,X2,X3) have Mult(l;1/3,1/3,1/3), and set h(l)=E|X2−X1||X3−X2|. Put c=2√3/(3π)+1/9 and a*=−2√3/(9π). The source proves that for each r∈{0,1,2}, as l→∞ along l≡r mod3,

    h(l)=c l+a*+b_r/l+O(l⁻²),
    b_r=d0+4√3/(9π) cos(2πr/3).

Definition 7.4 sets a_triangle=1/32+(π/9)Σ_r b_r. We prove d0=−4√3/(81π), hence a_triangle=1/32−4√3/243, exactly Conjecture 7.7. There is no additional varying n parameter in this constant; the source's all-fixed-n covariance consequences follow by its Lemma 7.5/Theorem 7.6 and receive no separate credit.

## Extracting the entire origin coefficient

Write Φ(x,y)=(e^(−ix)+e^(i(x−y))+e^(iy))/3. The exact Fourier identity (6.7) is h(l)=(2π)⁻²⟨S⊗S,Φ^l⟩ on the torus, with the tensor Abel finite part and S(x)=−1/(2sin²(x/2)). By Lemma 6.6 its local expansion is

    S(x)=−2 fp(x⁻²)−1/6−x²/120+O(x⁴).

Let log Φ(tu,tv)=Σ_(k≥2) t^k B_k(u,v). Then B2=−(u²−uv+v²)/3. With G=exp(B2), define

    P2=B4+B3²/2,
    P4=B6+B3 B5+B4²/2+B3² B4/2+B3⁴/24.

These are the t² and t⁴ coefficients after the central scaling Φ(u/√l,v/√l)^l=G(1+l⁻¹/² B3+l⁻¹ P2+…+l⁻² P4+…). Odd total degree terms integrate to zero under simultaneous (u,v)↦(−u,−v), including against the finite parts. Only simultaneous parity is needed.

Use the source's symmetric origin cutoff. Scaling and multiplying the two kernels and the Jacobian show that the coefficient of l⁻¹ in this origin contribution is exactly

    d0=I(4P4/(u²v²))
       +I((1/3)(u⁻²+v⁻²)P2)
       +I((1/60)(v²/u²+u²/v²))
       +I(1/36),                                      (A)

where I(F)=(2π)⁻²⟨F,G⟩ and negative powers are Hadamard finite parts (principal values for power −1). In particular the smooth×smooth term and the quadratic terms in the regular kernel cannot be dropped.

This is an asymptotic identity with a controlled remainder, not an exchange justified by a numerical integral. Specifically the s=5 expansion in the proof of source Lemma 7.3 has remainder O(l⁻³) in the Gaussian-weighted C^(2,2) seminorm. Its tensor singular piece has outside factor l and therefore remainder O(l⁻²). The mixed pieces have outside factor 1: expansion through P2, with the odd P3 term vanishing, leaves O(l⁻²). The regular×regular piece has outside factor l⁻¹ and leading constant 1/36; its next nonzero term is O(l⁻²). The next kernel Taylor terms similarly start at O(l⁻²). Gaussian tails permit replacing the expanding origin window by R² at every retained order. The source's finite-part continuity bound (Lemma 6.7) controls these replacements. Off the three saddles contributions are exponentially small. At the two twisted saddles the source's exact phase identity gives the already displayed cosine term, whose residue average is zero. Thus (A) computes precisely the source d0.

## Exact finite arithmetic for (A)

Here is a finite-sum evaluation method, independent of numerical quadrature. Put

    f_k=i^k[(-u)^k+(u−v)^k+v^k]/(3 k!), f_0=1,
    B_k=f_k−(1/k)Σ_(j=1)^(k−1) j B_j f_(k−j).

This follows by differentiating exp(Σ B_k t^k)=Σ f_k t^k; B1=0. It determines every polynomial used in (A) by six finite steps. For transparency the nonquadratic inputs are

    B3=i(u²v−uv²)/6,
    B4=−u⁴/36+u³v/18−u²v²/12+uv³/18−v⁴/36,
    B5=i(u⁴v−2u³v²+2u²v³−uv⁴)/24,
    B6=−13(u⁶+v⁶)/3240+13(u⁵v+uv⁵)/1080
       −5(u⁴v²+u²v⁴)/432+u³v³/324.

Define M_k=fp∫_R z^k exp(−z²/4)dz. For the indices needed here,

    M_(−2)=−√π; M_k=0 for odd k≥−1;
    M_k=2^(k+1) Γ((k+1)/2) for even k≥0.

The first identity follows from fp(z⁻²)=−(pv z⁻¹)' by integration by parts; the rest are elementary Gaussian moments. Every monomial u^p v^q in (A) has at least one nonnegative exponent and both exponents ≥−2. Exchange u and v if necessary so p≥0. Completing the square u²−uv+v²=(u−v/2)²+3v²/4 gives the exact rule

    I(u^p v^q)=√(3π)/(4π²) Σ_(j=0)^floor(p/2)
        binom(p,2j)(2j−1)!! (3/2)^j 2^(−p+2j) M_(p−2j+q),

with (−1)!!=1. Distributional integration is valid here since the inner Gaussian polynomial integral is a Schwartz function of the remaining variable. Linearity, this rule and the displayed B_k give:

|Piece of (A)|Exact value|
|---|---|
|pure singular × P4|−11√3/(405π)|
|two mixed singular × P2|−√3/(36π)|
|two quadratic regular-kernel terms|−√3/(120π)|
|regular × regular|√3/(72π)|

Consequently d0=(√3/π)(−11/405−1/36−1/120+1/72)=−4√3/(81π). Since Σ_(r=0)^2 cos(2πr/3)=0, Definition 7.4 yields a_triangle=1/32+(π/3)d0=1/32−4√3/243. This proves the complete literal source conjecture. ∎

exact.py reproduces the finite arithmetic with exact rationals and radicals; exactchecks.json records the expanded polynomials and zero discrepancy. This script checks arithmetic and is not a premise replacing the displayed finite evaluation rule. lattice.py independently checks exact conditional binomial sums against the three-step distribution recurrence for l≤30, then checks the three residue asymptotics through l=362. Those finite values are supporting diagnostics, not a proof of a limit.

Novelty/substance limit: the source already proves existence and identifies the needed saddle. Computing its unevaluated next coefficient may be judged a routine completion of that framework. No claim of worldwide novelty, accepted discovery, or automatic eligibility is made. Current public-registry heads remain unavailable under inherited access denials; the proof can be reviewed independently of that unresolved credit gate.
