# Focused eligibility and corrected-priority review

Recommendation: **HOLD**, with ordinary MATH PASS retained. Do not accept or count. This focused review does not establish either a sound earlier square-root proof or a pre-existing theorem whose hypotheses supply the logarithmic Abel monotonicity automatically. It does establish a precise, serious classical-corollary objection and the exact remaining mathematical distinction. Counts are administrative only: 9 additional / 39 total / next 40; root alone adjudicates.

The literal assertion is that the diagonal operator with coefficients gamma_k=sqrt(k)/k! preserves real-rootedness of every real polynomial, including mixed-sign roots and the zero-polynomial convention. It is not the CZDS assertion. The frozen candidate is unchanged. Its false wholesale-omission account is superseded by the frozen root `CORRECTION.md`, originally `../root-multiplier-history-correction-r2/CORRECTION.md`.

## What the focused primary-body investigation establishes

The principal additional primary body is Cho–Chung–Park, *Partial fraction expansions and zeros of Hankel transforms*, [arXiv:2311.04385v2](https://arxiv.org/pdf/2311.04385v2), dated 8 November 2024 (v1 public 7 November 2023). The actual PDF was downloaded, hash-frozen before extraction/reading, and its definitions, Theorems 2.1, 4.1, 5.1, 5.2, Lemmas 6.1–6.2, Theorem 6.1 and relevant proofs read. This is a theorem-body comparison, not clearance inferred from its abstract.

In its normalization, Jcal_nu(z)=Gamma(nu+1)(z/2)^(-nu)J_nu(z), and Hcal_nu(f)(z)=integral_0^1 t^(nu+1/2) f(t) Jcal_nu(zt)dt. Theorem 6.1 (PDF p30) assumes nu>-1, positive integrable f, and additionally integral t^(nu+1/2)|f| finite if nu<-1/2. For |nu|<=1/2, f must increase, with the finite rational-step exceptional case excluded at equality. For |nu|>1/2 it instead requires t^(3/2-3|nu|)f(t) increasing. It concludes LP membership and all real simple zeros, with the stated Bessel-zero interlacing. Lemmas 6.1–6.2 prove the required sample signs by Sturm comparisons. Theorem 4.1 (pp20–21) and Theorem 5.1 (p23) allow -1<mu<nu+2 but require sign alternation at **every** j_mu,m; this is a hypothesis, not an automatic consequence of positivity.

Direct specialization of the candidate's Bessel moment has nu=0 and f(t)=C t^(1/2)sqrt(-log t), C>0, since u=t^2. It satisfies positivity and integrability, but

`f'(t)/f(t) = (1/(2t)) (1 - 1/(-log t))`.

It increases only before t=e^-1 and decreases thereafter. Thus the direct Hankel monotonicity hypothesis fails. The arbitrary-mu sign theorem does not repair this without an independent infinite sign proof. Alternatively nu=1/2 with f=h does supply the sine-transform conclusion, since Jcal_(1/2)(z)=sin(z)/z: Hcal_(1/2)(h)=V(z)/z. All its hypotheses then hold, **after** proving h increasing. This is exactly the old Pólya endpoint in newer Hankel notation, not a theorem making the Abel step automatic.

Theorem 5.2 (pp23–25) is also relevant to the fractional-Euler objection. Its full assumptions are an even entire LP function G=sum (-1)^m gamma_m z^(2m)/m!, nonzero real gamma_m=O(1/m!). It concludes (z d/dz+alpha)G in LP for alpha>=0. The proof uses its genus-zero product and logarithmic derivative. Alpha is an additive constant, not the power of an operator. Repeated application multiplies coefficients by products of linear factors; it does not authorize coefficient multiplication by sqrt(m), nor fractional powers of the Euler operator. In particular a claim of unrestricted fractional-Euler LP closure would contradict the source's explicit small-exponent failure.

A bounded current Le Roy search also led to Dattoli–Ricci, *Le Roy, Lerch and Legendre chi functions and generalised Borel-Le Roy transform*, [arXiv:2603.12164v2](https://arxiv.org/pdf/2603.12164v2), 17 March 2026. The actual body was frozen/read for the fractional-operator and reciprocal-power formulas, notably (2), (33)–(35), and the Borel/summability discussion (49)–(52). Formula (33) extends an umbral ground-state evaluation using Gamma(1+lambda)/(lambda+alpha)^s where nonsingular; it is not a zero-preservation theorem on all LP functions. No real-zero conclusion follows from these formulas. Its bibliography points to Garra–Polito on Hadamard derivatives (2013), whose body was not retrieved here; that reference remains an explicit specialist gap. I do not claim a comprehensive fractional-calculus audit or elevate this 2026 formalism into a classical subsumer.

The already immutable Cho–Park [2110.01885v1](https://arxiv.org/pdf/2110.01885v1), 5 October 2021, was independently re-read at Theorem 2.1 and Section 3, especially (3.4), pp4–9. Its positive-decreasing sine positivity and integrable-kernel partial fractions supply the classical part completely. Its introductory positive-real-zero wording alone would not suffice. The later Hankel body's (1.6) appears to omit the sample divisor m*pi present in the 2021 (3.4); this review uses the correct 2021 identity, not that displayed later introductory transcription. The 2024 general theorems are used only with their stated hypotheses.

## Independent bridge check relevant to substantive eligibility

Let F(x)=sum_(k>=1) sqrt(k)x^k/(k!)^2 and H(z)=F(-z^2/4)/(-z^2/4), H(0)=1. The identity sqrt(n+1)/((n+1)!)^2=1/((n!)^2(n+1)^(3/2)) and the Gamma moment give

`H(z)=(2/sqrt(pi)) integral_0^1 sqrt(-log u) J0(z sqrt(u))du`.

The arcsine representation of J0 gives H=4/(pi sqrt(pi)) integral K(t)cos(zt)dt with K(t)=integral_(t^2)^1 sqrt(-log u)/sqrt(u-t^2)du. Uniform absolute convergence on compact z-sets and integrability of the nonnegative log/arcsine weights justify both steps.

To check the genuinely object-specific part independently, write sqrt(-log u)=(1/2)integral_u^1 ds/(s sqrt(-log s)). Tonelli yields

`K(t)=integral_(t^2)^1 sqrt(s-t^2)/(s sqrt(-log s))ds`,

`h(t)=t integral_(t^2)^1 ds/[s sqrt(-log s)sqrt(s-t^2)]`.

A second Tonelli interchange uses integral_t^sqrt(s) v/sqrt(s-v^2)dv=sqrt(s-t^2) and proves K(t)=integral_t^1 h(v)dv, including endpoints. Thus absolute continuity is established without differentiation at a moving singular endpoint. Substituting s=t^2+v^2, v=t tan(theta), r=-log cos(theta), and a=-log t gives exactly

`h(e^-a)=integral_0^1 g(au)/sqrt(u(1-u))du`,

`g(r)=sqrt(2r/(exp(2r)-1)), g(0)=1`.

The derivative numerator for 2r/(exp(2r)-1) is 2[exp(2r)(1-2r)-1], strictly negative for r>0. Hence g strictly decreases and 0<g<=1. Dominated convergence proves h(0)=0, h(1)=pi, and strict increase. These constants agree with K(0)=sqrt(2pi). This is a real, exact bridge, not an assumed closure property of multiplier sequences.

For completeness the downstream classical-to-literal chain is short enough to specify fully. Integration by parts gives H=4V/(pi sqrt(pi)z), V=integral h(t)sin(zt)dt. Pairing consecutive half-waves of the strictly decreasing h(1-t) proves c_k=(-1)^k V(k*pi)/(k*pi)<0. The correct integrable-kernel identity (2021 (3.4)) gives, with w=z^2,

`V(z)/sin z=V'(0)+sum_(k>=1) 2 c_k w/(w-k^2*pi^2)`.

Bounded variation of h gives c_k=O(k^-2), so the series and imaginary-part calculation converge locally away from poles. Each summand's imaginary part is -2c_k k^2*pi^2 Im(w)/|w-k^2*pi^2|^2, of the strict sign of Im(w). For z=iy!=0 the quotient is integral h(t)sinh(yt)dt/sinh(y)>0. Thus V has no nonreal zeros. Its real sampling poles are not zeros; zero is simple. Every nonzero zero of F is therefore negative. Stirling and the coefficient order formula give order 1/2; Hadamard supplies F(x)=x product(1+x/r_j), r_j>0, sum 1/r_j finite. Its finite products put it in LP+. Csordas–Forgács Theorem 6 gives exactly the all-real-rooted-polynomials multiplier endpoint. No finite Jensen checks or CZDS implication enter.

## Diagnostic exponent calculation and adjudication

This diagnostic tests automaticity; it is not proposed as a new broader credited theorem. For 0<s<1 put beta=1-s and replace the log weight by (-log u)^beta. The same nonnegative Tonelli step gives

`K_beta(t)=2 beta integral_(t^2)^1 sqrt(v-t^2)(-log v)^(beta-1)dv/v`,

`h_beta(t)=2 beta t integral_(t^2)^1 (-log v)^(beta-1)dv/[v sqrt(v-t^2)]`.

The same substitutions give the exact scaling identity

`h_beta(e^-a)=2^(beta+1/2) beta a^(beta-1/2) integral_0^1 (1-u)^(beta-1)u^(-1/2)g(au)du`.

At beta=1/2 the prefactor is exactly one and its power of a vanishes. For 0<beta<1/2 both positive factors decrease in a. For beta>1/2 the expression tends to zero as a->0, so the desired increasing-positive-in-t hypothesis cannot hold (it would force its right limit to dominate positive interior values). The square-root exponent is the boundary where this elementary monotonicity argument works with bounded h. This does not refute any other exponent's conclusion; it diagnoses failure of this particular sufficient condition. It also explains why generic log-moment positivity or integer-Euler closure cannot supply the result automatically.

**Strongest exclusion case:** Gamma moments, the Bessel arcsine formula, Tonelli, the substitutions above and monotonicity of r/(e^(2r)-1) are standard operations. Once h's formula is recognized, everything else is an explicit specialization of classical Pólya–Schur/Fourier zero theory. A strict campaign may judge this recognition and one-kernel calculation a routine application; proof length and an old open label cannot defeat that objection.

**Strongest favorable case:** the closest actual general Hankel theorem fails its direct hypothesis, fractional-Euler closure is unavailable, and the exact Abel/log interaction cancels an exponent precisely at 1/2. Establishing the transformed kernel's monotonicity is not a hypothesis already supplied by the bodies checked. No located theorem in this review identifies the log kernel or proves its monotonicity as a named special case. Excluding on the assertion that such a theorem exists would overstate the evidence.

Accordingly SUBSTANTIVE remains HOLD, not automatic INVEST or categorical EXCLUDE. The nonautomatic contribution currently identified is **the exact Abel representation and monotonicity for this logarithmic Bessel moment**. Its status as sufficiently substantive new work is still contested. Root must either justify that contribution against the complete routine-calculation objection, or exclude explicitly on that standard; this review supplies no independent campaign-level novelty PASS.

## Corrected chronology and remaining gates

Actual immutable source bodies checked here establish: Csordas–Forgács v2 (26 August 2015), Example 20, gives a small positive exponent failure and square-root numerical evidence; Problem 39 separates (a) multiplier and (b) CZDS. Baricz–Singh v1 (2 February 2017) explicitly asserts all s>0 in Theorem 6 and expressly says the sqrt case is settled. Its proof calls z^s/Gamma(z+1) entire/LP, invalid for noninteger s at zero. This is an earlier **public assertion**, not a verified valid supplier. A bad proof of the all-s claim neither makes the sqrt conclusion false nor proves priority for this candidate.

Baricz–Singh v2 (16 August 2017) **retains Theorem 6**, restricts s to N0 and removes the sqrt-settled paragraph. Theorem and proof occur on PDF pp6/10; v1 Theorem/proof on pp7/11 in the reused PDF (printed and PDF pagination should not be conflated). Root's correction adopts this account. Journal DOI 10.1090/proc/13927, online 12 January 2018 according to the inherited Crossref record, is still an unread final body. A fresh lawful OpenAlex location query lists only the publisher and arXiv submitted version, no distinct institutional/author final body. No such body or correction was identified by this bounded search. No publisher PDF, alternate publisher path or forbidden access route was retried. Do not certify arXiv v2 as the final journal text or claim no erratum exists.

Remaining gates before acceptance: (1) root's reasoned substantive ruling on the exact Abel calculation; (2) final-journal/possible-correction history resolved through an actually distinct lawful body, or explicitly held rather than silently cleared; (3) bounded but adequate specialist Hadamard/fractional-Euler and classical log-weight-transform coverage, including unresolved cited bodies; (4) current public-registry coverage, whose old inaccessible intervals remain parked. No Lean, manuscript, formal replay or count was attempted or authorized here. Ordinary MATH PASS does not clear these gates.

## Evidence, access limits and integrity

`freeze.json` binds immediate candidate/review/root-correction inputs before scientific reading. `references.json` hashes the existing immutable primary PDFs/texts in the preliminary review lane: they are reused in place, with no historical tree recopy. `admin/` is a snapshot only; original ledger/context files are not treated as scientific frozen sources. `before-after.json` records independent final original/copy checks. `retrieval/*.receipt.json` preserves exact URLs, query strings, UTC access times, statuses and failures. New PDFs have a separate pre-reading freeze record; extracted texts are derivative evidence.

Bing returned HTTP 200 pages whose results were plainly off-topic (Henkel companies, bank locations, generic zeros). These are preserved search failures, not negative novelty evidence. arXiv query responses are bounded title/abstract discovery aids; only the actual two newly retrieved bodies above support the theorem comparisons. Empty fractional-Euler/correction query results do not clear those literatures. The logarithmic query also returned unrelated Hankel determinants. Contemporary registry clearance remains incomplete. No GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge route, browser, proxy, TLS override or access-control bypass was used. The earlier AMS 403 is inherited and parked; no new 403/429 occurred in these retrievals.

All Python, retrieval, pdftotext, edits by scripts and hashing ran through the specified helper_guard with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1; AS and sampled group RSS 512 MiB, CPU 210 s, wall 230 s, unchanged. Native bounded reads and apply_patch were also used as permitted. Group RSS is sampled, not a claim to rule out every transient. Final manifest excludes itself and the receipt; the separately invoked verifier hashes manifest entries, originals/copies and reused references after all writes. No shared/git/public/MathDB/Lean/manuscript edits, children or count changes.

## Exact primary PDF SHA-256 inventory

* `1505.00355v2.pdf`: `8bd09382fbce10278e3cb31732c949b2ec91ea4860d18a3e8669bf53f9c43bac` (immutable path in references.json).
* `polya2110.pdf`: `0e5a9f83fdd57970e38b4c8b26ba5c7c3a7d6aef825082262453dcb18a4bdd2a` (immutable path in references.json).
* `citer1702.pdf`: `e1d46cb4fdecb60f44082b5bf51810fc4874e0637bdbc5f06d9ef338be4bf100` (immutable path in references.json).
* `citer1702v2.pdf`: `992a42316a41b39027377cbb2690b908ee14f3c1e2464b23c9727316d882abc7` (immutable path in references.json).
* `citer2018.pdf`: `76a29a3500f8f9c5c19a59f127f92cf59619f14e736bba792bedbf724cdabd47` (immutable path in references.json).
* `retrieval/2311.04385v2.pdf`: `b60910ad5df40393ab8fc889cbb34bffe8fb7a7abd146aba79db6cceec59fdfc` (local frozen PDF).
* `retrieval/2603.12164v2.pdf`: `74c7eed5b26e73f9a360591b435963354411f20a1c4fe3eb632d5fbdf58fd97a` (local frozen PDF).
