# Corrected powered-binomial monotonicity reduction

29 October 2026 UTC. Root read sol-fresh-finite-source-r15/discovery.md.
Full Byun–Poznanović Conjecture 1.1(a) remains unresolved; credit 0.

Write D_r=sum(i=0..r) binom(r,i)^l a^(li), and
A_r=(r+1)^l(D_(r+1)/D_r-1). The handoff's displayed alleged equivalent
inequality for A_(r+1)>=A_r has two wrong signs. The CORRECT numerator,
after multiplying by the positive D_r D_(r+1), is

    E=(r+2)^l D_r D_(r+2)
       - ((r+2)^l-(r+1)^l) D_r D_(r+1)
       - (r+1)^l D_(r+1)^2.

For r=1,l=1,a=1, (D_1,D_2,D_3)=(2,4,8), A_2-A_1=1 and E=8.
The erroneous display gives 40, so it cannot be the cleared difference.
No previous full proof relied on this display; the worker claimed no proof.

The sufficient route itself survives: for the source u_r=(binom(m,r)a^r)^l,
Q_r=N_r/u_(r+1) satisfies Q_r=rho_r(1+Q_(r-1)) with
rho_r=((r+1)/(a(m-r)))^l. Hence Q_r increases, and Q_r/(r+1)^l also increases.
The source sign is sign(S_(r+1)-S_r)=sign(1-H_r), where
H_r=A_r Q_r/(r+1)^l. Thus positivity and monotonicity of A would establish
the necessary single crossing for all m. That monotonicity remains UNPROVED.

A tempting route is coefficientwise nonnegativity of E as a polynomial in
x=a^l for every integer l>=1. Its coefficients are differences of sums of
l-th powers of explicitly weighted binomial products. Generic weak
majorization of those product multisets is FALSE: at r=4 and coefficient
x^2, the sums of the largest two positive-side bases and negative-side
bases are 244 and 245 respectively. Thus arbitrary-convex-function
majorization cannot simply supply the power comparison. This does not
disprove coefficientwise positivity for the powers actually required.

Initial exact diagnostics found nonnegative corrected coefficients for
0<=r<=20, 1<=l<=40, every coefficient. These are finite checks only.
check.py reproduces these checks, the direct cleared-difference identity,
and the majorization obstruction within the fixed resource caps. No full
ordinary proof, source re-review, novelty clearance or Lean claim is made.

## A more precise all-order target (unproved)

Use binom(r,i)=0 outside 0<=i<=r. For each r>=0 and 0<=j<=2r+2 form two
multisets, each indexed twice by i=0,...,r+2:

    P = {(r+2) binom(r,i) binom(r+2,j-i)}
        union {(r+1) binom(r,i) binom(r+1,j-i)},
    N = {(r+2) binom(r,i) binom(r+1,j-i)}
        union {(r+1) binom(r+1,i) binom(r+1,j-i)}.

The coefficient of x^j in corrected E (where x=a^l) is exactly
sum(P_i^l)-sum(N_i^l). Although P does not weakly majorize N in general,
their SQUARES passed weak majorization for all 3843 pairs with 0<=r<=60.
This is not an all-order proof. Precisely, the unproved assertion says that,
after sorting each list in descending order, every prefix sum of P_i^2
is at least the corresponding prefix sum of N_i^2.

If that assertion holds for every r,j, classical weak-majorization
preservation under the increasing convex function t^(l/2), l>=2, proves
coefficientwise E>=0 for all integer l>=2. The l=1 case is the exact identity
E=x(1+x)^(2r+1). This would prove A monotone and therefore full source
unimodality. Weak majorization and convex-power preservation are classical
tools, uncredited; the all-r,j binomial assertion is the missing bridge.

The checker independently verifies 240 cleared-difference identities,
19320 coefficients and the 3843 squared-majorization cases. This target
is more specific than simply asking for more finite source checks, but it
may itself be false at larger indices; a falsifier would defeat this route
only, not the original conjecture.

Root freshly read arXiv:2604.14639v1's literal (1.4), Conjecture1.1(a),
and Theorem1.2 via the public HTML on29October. The target is all positive
integer m,l and real a>0. The known l=2,a=1 result is not credited. The
worker's later-source screen remains bounded and was not independently
repeated here; no current novelty clearance follows from this source read.

The analytic r16 handoff was also read: logarithm–arctangent Conjecture4.7
remains unresolved. Its global derivative cancellation is missing; no
partial local/asymptotic observation earns credit. Both completed handoffs
leave counts 3/30 additional and 33/60 total unchanged.
