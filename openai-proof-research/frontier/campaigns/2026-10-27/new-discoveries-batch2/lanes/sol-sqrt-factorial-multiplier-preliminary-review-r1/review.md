# Independent preliminary review: square-root factorial multiplier

Recommendation: **HOLD**. The ordinary analytic proof survives this adversarial review, with a fully justified replacement for its most delicate integration step below. This is not an acceptance recommendation or a discovery count. The historical account contains a material, directly verified error. Substantive eligibility and contemporary prior-art clearance remain open. Administrative snapshot: 9 additional / 39 total / next 40; root alone decides/counts.

## Separate verdicts

| Gate | Verdict | Reason |
|---|---|---|
| SOURCE | Literal endpoint PASS; historical account CORRECTION REQUIRED | Source Theorem6, Section3.1/Example20 and Problem39(a) match sqrt(k)/k!, including k=0. Baricz–Singh v2 retains Theorem6 with integer scope; it does not omit it. Journal body remains unavailable. |
| MATH | PASS at ordinary analytic proof level | Coefficients, constants, absolute continuity, strict even/odd signs, exact partial fractions, exclusion of all nonreal zeros and genus-zero factorization check out. See independent derivation below. No stronger CZDS claim. |
| SUBSTANTIVE | HOLD; strong routine-corollary objection | Full bridge to classical Pólya partial fractions is exhibited below. The only object-specific work is obtaining the kernel and its Abel monotonicity. That is real work but does not by itself establish campaign-level substantive novelty. |
| NOVELTY | HOLD / not cleared | Explicit 2017 public assertion exists, with a defective proof and a later integer restriction. No sound prior square-root resolution verified. Journal final body, later corrections, specialist transform coverage and current public registries remain bounded gaps. |
| FORMAL-FEASIBILITY | Plausible in principle; NOT demonstrated | Requires substantial analytic infrastructure, not merely finite algebra. No Lean written or checked. No formal endpoint or strict replay exists in this review. |

## Independent mathematical audit

Put F(x)=sum_{k>=1} sqrt(k)x^k/(k!)² and H(z)=F(-z²/4)/(-z²/4). Its value at zero is 1, since F'(0)=1. The coefficient identity sqrt(n+1)/((n+1)!)²=1/((n!)²(n+1)^(3/2)) is exact. The Gamma moment and arcsine cosine integral give

H(z)=(2/sqrt(pi)) integral_0^1 sqrt(-log u) J0(z sqrt(u))du
    =4/(pi sqrt(pi)) integral_0^1 K(t)cos(zt)dt,

K(t)=integral_{t²}^1 sqrt(-log u)/sqrt(u-t²)du.

These are entire identities: on |z|<=R, the Bessel series is absolutely uniformly bounded by sum (R²/4)^n/(n!)². The logarithmic weight is integrable. The absolute arcsine inner integral is bounded by (pi/2)exp(R), so Fubini applies. All constants, the factor4 and the sign in F(-z²/4) were independently rederived. At endpoints K(0)=Gamma(3/2)/(1/2)^(3/2)=sqrt(2pi), K(1)=0. Dominated convergence in K(t)=2 integral_0^sqrt(1-t²) sqrt(-log(t²+v²))dv follows by extending the integrand by zero to [0,1] and dominating it by 2sqrt(-2log v).

### A replacement that avoids moving-endpoint differentiation

For 0<u<1,

sqrt(-log u)=(1/2) integral_u^1 ds/(s sqrt(-log s)).

Nonnegative Tonelli therefore gives

K(t)=integral_{t²}^1 sqrt(s-t²)/(s sqrt(-log s))ds.

Define, initially for 0<t<1,

h(t)=t integral_{t²}^1 ds/(s sqrt(-log s) sqrt(s-t²)).

Changing s=t²+v² yields exactly the candidate's formula(2). With a=-log t and v=t tan(theta), r=-log cos(theta), its formula(3) follows with NO missing factor:

h(e^-a)=sqrt(2) integral_0^a dr/[sqrt(a-r)sqrt(exp(2r)-1)]
        =integral_0^1 g(au)/sqrt(u(1-u))du,
g(r)=sqrt(2r/(exp(2r)-1)), g(0)=1.

The derivative of exp(2r)(1-2r)-1 is -4r exp(2r)<0. Hence g is strictly decreasing, 0<g<=1, with limit0 at infinity. The integrable dominating function [u(1-u)]^-1/2 proves by DCT continuity, h(0+)=0 and h(1-)=pi; strict inequality on u in (0,1) proves strict increase in t. Thus 0<h<pi and h extends continuously to [0,1].

A second application of nonnegative Tonelli gives, for every t in [0,1],

integral_t^1 h(v)dv
=integral_{t²}^1 [integral_t^sqrt(s) v/sqrt(s-v²)dv] ds/(s sqrt(-log s))
=integral_{t²}^1 sqrt(s-t²)/(s sqrt(-log s))ds=K(t).

This proves absolute continuity and K'=-h directly, including both endpoints in the integral representation. It supplies a rigorous alternative to the draft's abbreviated differentiation justification. No assumption of endpoint differentiability is needed. Integration by parts now gives H(z)=4V(z)/(pi sqrt(pi)z), V(z)=integral_0^1 h(t)sin(zt)dt. At z=0 this is removable; V'(0)=pi sqrt(pi)/4>0. Consequently F(-z²/4)=-zV(z)/(pi sqrt(pi)), as claimed.

### Signs, exact identity and complex zeros

Let f(s)=h(1-s), strictly decreasing and positive on (0,1). For integer k>=1, write I_k=integral_0^1 f(s)sin(kpi s)ds. For k even, pair intervals [2j/k,(2j+1)/k] and [(2j+1)/k,(2j+2)/k]. Their sum is

integral_0^(1/k) [f(2j/k+r)-f((2j+1)/k+r)] sin(kpi r)dr>0.

There are k/2 such pairs. For k odd there are (k-1)/2 positive pairs and a positive final half-wave. This includes k=1. Thus I_k>0, V(kpi)=(-1)^(k+1)I_k, and c_k=(-1)^k V(kpi)/(kpi)<0. In particular no pole kpi is a zero of V. This is also covered by the actual Cho–Park Theorem2.1, whose full half-wave proof, including its even-m case, was read.

The frozen actual Cho–Park v1 PDF pp7–9 explicitly states equation(3.4) under integral_0^1 |f|<infinity:

V(z)/(z sin z)=V'(0)/z + sum_{k>=1} c_k(1/(z-kpi)+1/(z+kpi)).

There is no extra z or missing constant in the candidate's transcription. The source explains the contour/Liouville derivation of(3.2) and states(3.3),(3.4) in the same manner. Independently, (3.4) is (3.2) applied to K: its cosine transform is V/z, its value at0 is V'(0), and its sample at kpi is V(kpi)/(kpi). This verifies the exact specialization rather than relying on a positive-real-zero summary.

Since h is bounded monotone with total variation pi, Stieltjes integration by parts gives |V(kpi)|<=2/k and |c_k|<=2/(pi k²). After multiplication by z the series is

V(z)/sin z=V'(0)+sum_{k>=1} 2c_k w/(w-k²pi²), w=z².

On every compact w-set avoiding the poles the tails are bounded by a constant times sum k^-4. This proves locally uniform absolute convergence and legitimizes imaginary parts. For Im(w) !=0 the kth imaginary part is -2c_k k²pi² Im(w)/|w-k²pi²|², strictly of the sign of Im(w). The sum cannot vanish. If z is nonreal and w real, then z=iy, y real nonzero; V(iy)/sin(iy)=integral h(t)sinh(yt)dt/sinh y>0. The two cases cover every nonreal z. The zero at0 is simple because V'(0)>0; sin has no nonreal zeros, and all its nonzero real poles have nonzero V. No cancellation gap remains.

Every nonzero zero x of F therefore satisfies x=-z²/4<0. The coefficient order formula with Stirling gives order exactly1/2. Hadamard at order<1 supplies a genus-zero product x times product(1+x/r_j), r_j>0, sum1/r_j finite, with constant1 from F'(0)=1 and no nonconstant exponential polynomial. The finite products converge locally uniformly and have only nonpositive zeros. Thus F is in LP+, and the source Theorem6 yields the exact classical multiplier endpoint for every polynomial. This proves all orders analytically; the finite controls do not supply this conclusion.

## Historical/source correction and bounded novelty

Actual bodies, not inherited assertions, establish the following.

* Csordas–Forgács v2 Example20 explicitly gives s=1/20 as a failure, with a sixth Jensen polynomial, and reports square-root numerical evidence only. Problem39 separates multiplier and CZDS questions. The literal endpoint here is solely part(a).
* Baricz–Singh v1, submitted 2 February 2017, PDFp6 Theorem6 explicitly asserts all s>0 and the preceding paragraph specifically claims to settle s=1/2. Its proof p11 uses z^s/Gamma(z+1) as an entire LP function. For noninteger s this fails at0; the all-s claim also conflicts with Example20. This is an earlier public assertion of the literal endpoint, not a verified sound prior proof. A defect in that proof alone would not establish falsity of its square-root conclusion.
* Baricz–Singh v2, submitted 16 August 2017, PDFp6 **retains Theorem6**, restricted to s in N0; its preceding paragraph states the integer/m=2 case, and the proof remains on p10. The original square-root-settled paragraph is removed. The reviewed candidate's claim of wholesale theorem omission is false and must be corrected. The observed narrowing is a correction in scope; no evidence here establishes why or when the authors recognized the defect. At s=0 the proof's wording about a zero at0 also needs care but has no bearing on s=1/2.
* DOI10.1090/proc/13927 resolves to the AMS journal landing page. Crossref records online publication 12 January 2018, issue146(5). The canonical journal PDF returned403 and was not retried. No accessible distinct institution/author body was identified by the bounded DOI/OpenAlex location check. Neither the landing HTML nor arXiv v2 is certified to be the final journal body. No later erratum absence is claimed from an empty metadata relation field.

`evidence.md` identifies exact page/text locations; frozen full bodies and `freeze.json` bind these observations. Dates are submission/publication dates, not server modification dates. Current complete registry and specialist Fourier/Hankel prior-art audits were not available; forbidden historical routes were parked. The candidate's compact prior-screen evidence is not upgraded into independent exhaustive clearance.

## Substantive objection and residual gates

The complete classical-to-literal bridge is displayed above: Gamma moment -> arcsine cosine transform -> positive logarithmic K -> Tonelli/Abel formula for h -> strictly increasing bounded kernel -> half-wave signs -> classical partial fractions -> negative zeros -> genus-zero LP+ -> literal source multiplier endpoint. Equivalently K is positive decreasing concave and -K' is strictly increasing, fitting the classical concave-cosine/increasing-sine transform setting. General-case hypotheses hold since neither h nor its reflection is piecewise constant. Convexity of h is not required. The positive-real-zero wording in Cho–Park's TheoremA/B alone is insufficient to exclude complex zeros; the actual partial fractions above close that point.

This is a serious complete routine-corollary objection, not an unsupported “old tools” label. However, this review did not locate an older theorem already written for this logarithmic Hankel kernel, nor establish that recognizing and proving the Abel monotonicity is automatic from a general prior result. A short substitution alone cannot certify novelty or non-novelty. I therefore do not issue a final EXCLUDE solely because the proof is short, and do not grant substantive PASS solely because the question was posed open.

Concrete residual gates before significant formalization or any acceptance:

1. Correct the false v2-omission account, preserving the earlier explicit square-root assertion and actual integer restriction.
2. Obtain a lawful distinct primary journal/author/institution final body or subsequent correction body; inspect its actual Theorem6 scope/proof. Do not retry the403 publisher route or alternate paths to the same body.
3. Root adjudicate the complete classical bridge under the campaign's no-routine-corollaries standard, with a focused primary-body Fourier/Hankel/logarithmic-kernel subsumption check. No discovery credit based on an open label.
4. Clear current prior-art/registry gaps only through authorized accessible sources, without repetitive historical loops; retain bounded caveats.
5. If still eligible, produce a literal formal endpoint and strict independent replay. Hard formal bridges include complex integral identities, Tonelli/DCT, the sampling identity, locally uniform meromorphic series, order/Hadamard factorization and Pólya–Schur. This review provides no evidence those are already available in the project's Lean environment. Do not replace them with finite Jensen checks or imported unproved assertions.

The strongest mathematical stress point was singular-endpoint justification; the Tonelli argument resolves it. The strongest remaining objection is substantive/classical subsumption, compounded by incomplete journal and current-prior evidence. Recommendation remains HOLD; no Lean/manuscript/shared/count edits were made.
