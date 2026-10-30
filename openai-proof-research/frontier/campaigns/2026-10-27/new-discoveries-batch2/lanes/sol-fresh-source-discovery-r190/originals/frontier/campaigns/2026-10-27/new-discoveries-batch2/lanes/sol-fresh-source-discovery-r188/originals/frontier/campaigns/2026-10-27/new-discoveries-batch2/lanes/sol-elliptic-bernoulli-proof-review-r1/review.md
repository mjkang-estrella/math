# Independent proof and eligibility review

2026-10-29. SOLO; credit 0. Recommendation: **HOLD overall. Ordinary proof PASS for the literal arXiv definition; substantive eligibility PASS at the bounded-investigation level, rather than EXCLUDE.** Do not begin formalization on this report. The published-source comparison remains unresolved. This is a review recommendation, not root adoption, acceptance, priority certification, or a count change (5/30 additional, 35/60 total).

## Decisive finding

The candidate has supplied an all-order proof, including the missing identification of the literal derivative-square periods with positive invariant derivatives of Laurent coefficients. I independently checked that identification and its analytic hypotheses. The worker's separate recommendation to exclude does not follow just from the cited heat theorem. Its actual §8.4 Theorem 37 concerns sigma and invariant differential operators; it contains neither the derivative-square periods nor their period-correlation generating function. The positive Laurent recurrence in the source also does not identify these periods. The bridge in PROOF.md §2(C)-(D) is the problem-specific mathematical content.

I therefore do **not** recommend adopting the worker's blanket routine-corollary exclusion. Under the supplied campaign calibration this identification is sufficient for continued source/prior-art investigation. This is a substantive judgment, not a theorem of non-subsumption: a published period-product or equivalent generating-function antecedent could reverse it. No such actual body was located in this bounded review. The independent new institutional retrieval described below improves access evidence but does not clear the published-source gate. Overall HOLD is based on that gate, not on shortness or on unproved algebra.

## Precise object and mathematical verdict

Let g2,g3 be arbitrary complex numbers with g2^3 != 27g3^2. Uniformize y^2=4x^3-g2*x-g3 by x=p(z)=wp(z), y=p'(z), dz=dx/y. A cycle means a piecewise smooth closed cycle on this curve avoiding infinity, or a finite linear combination of such cycles. Write 2*omega=integral dz and -2*eta=integral p dz on that cycle. Source Definition (21), p11, is B_(2m)=1/2 integral (p^(m-1))^2 dz; the superscript denotes differentiation, not a power.

With p(t)=t^-2+sum_(r>=2)c_r*t^(2r-2), and delta=6g3*d_g2+(g2^2/3)*d_g3, the proof establishes for every m>=2

    B_(2m)=(-1)^(m-1) ( (2m-2)! delta(c_m) omega
                               - 2m(2m-2)! c_m eta ).

Both polynomials have strictly positive rational coefficients on their entire weighted supports. This is coefficient positivity in Q[g2,g3], not positivity of their values at complex invariants. No real ordering, preferred real period, or restriction to g2,g3>0 enters. At m=1 the literal result is g2*omega/12, with zero eta polynomial (empty support). No assertion about the stronger full-lambda Conjecture 1 is proved here.

### Heat identity and independent local verification

I read the actual Buchstaber–Bunkova §8.4 body, including the curve normalization, periods, Legendre relation, and Theorem 37; I also inspected the cached page15 image. Its Q2*sigma=0 gives delta(log sigma)=(-p+zeta^2)/2+g2*t^2/24. Applying -d_t^2 gives p''/2-p^2+zeta*p'-g2/12 = 2p^2+zeta*p'-g2/3. The coefficients and signs in the candidate are correct.

The candidate's separate ODE verification is valid: W=2p^2+zeta*p'-g2/3 satisfies W''-12pW=-3g3, as does delta p. Matching t^2 and t^4 removes the possible regular homogeneous resonance t^4; the remaining even series starts at t^6, where j(j-1)-12 cannot vanish. Analytic convergence of the Laurent expansions then yields the local identity. Here derivatives in g2,g3 are taken at fixed t. No differentiation of a varying period contour in invariant space is used anywhere in the period proof. This distinction avoids an otherwise serious Gauss–Manin convention problem.

### Pole matching, constant, and contours

For fixed sufficiently small nonlattice t, p(z)p(z+t) has principal parts p(t)/z^2+p'(t)/z at 0 and p(t)/(z+t)^2-p'(t)/(z+t) at -t. The claimed p(t)(p(z)+p(z+t))+p'(t)(zeta(z)-zeta(z+t)) has exactly these parts. The difference is entire elliptic, hence constant. At z=0 this constant is p''(t)/2-p(t)^2+p'(t)zeta(t)=2p(t)^2-g2/4+p'(t)zeta(t). In particular the -g2/4 here and -g2/3 in the heat identity are different and both correct.

Choose a lift of a compact representative cycle and a uniform small disk of t for which the contour and its translated poles remain disjoint. The translation integral of p is constant, because its derivative is the integral of the exact differential d(p(z+t)). It equals -2eta. The zeta difference is single-valued on the torus; its t derivative integrates to -2eta and its value at t=0 is zero, so its integral is -2eta*t. This is not an assumption that zeta itself is periodic, nor an illicit independent shift across a pole. Thus

    1/2 integral p(z)p(z+t) dz
      = omega*(delta p(t)+g2/12)-eta*(2p(t)+t p'(t)).

The left side is holomorphic at t=0; all apparent poles on the right cancel. Uniform Taylor differentiation under the compact contour is legitimate. The coefficient at t^(2m-2) on the left is integral p*p^(2m-2)/(2(2m-2)!), which integration by parts m-1 times identifies with (-1)^(m-1) B_(2m)/(2m-2)!. All endpoint terms vanish on a lifted period because the functions and their derivatives are periodic. This proves both period coefficients at every order, not just a recurrence or numerical equality.

There is no hidden primitive-cycle restriction. Additivity handles general cycles; the relevant single-pole even elliptic differentials have zero residues, so small loops about infinity contribute zero. For each fixed nonsingular curve, the two basic cycles have nonzero Legendre determinant eta1*omega2-omega1*eta2=pi*i/2. Hence equality on both uniquely identifies the two coefficients. One cycle alone would not suffice. Polynomial identities are universal on the nonsingular locus; no division by g2 or g3 excludes the equianharmonic or lemniscatic cases.

### All-order positivity and endpoint convention

The source prints c2=g2/20, c3=g3/28 and c_r=3/((2r+1)(r-3))*sum_(s=2)^(r-2)c_s*c_(r-s), r>=4. All recurrence multipliers are positive. Induction gives full support 2a+3b=r: for a+b>=2 remove one weight2 or weight3 generator and the remaining weight is at least2. The required convolution term is present, including both repeated-generator base cases.

Delta sends g2^a*g3^b to 6a*g2^(a-1)*g3^(b+1)+(b/3)*g2^(a+2)*g3^(b-1). For every target of weight m+1, a preimage of weight m exists: (a+1,b-1) if b>=1, or (a-2,1) if b=0. In the latter case a>=2 for m>=2. All multipliers are positive. This proves strict positivity on both complete supports, at every order.

The printed B2=3g2*omega is visible in the actual arXiv p13 image and also occurs in the newly obtained institutional text. Definition (21) and p''=6p^2-g2/2 instead give B2=g2*omega/12. This discrepancy supplies no credit and does not affect Conjecture 2's sign assertion. The zero Bhat at m1 is interpreted on empty support, consistently with source zero period polynomials. Degenerate discriminant curves are not part of the nonsingular theorem; no claim about their arbitrary singular cycles is needed.

## My independent exact diagnostic

checker.py was written from scratch without using or executing the candidate's exact_checks.py. It uses sparse rational polynomial arithmetic and a different integration route: form the literal square in Laurent series, then subtract the even derivatives p^(2k), k>=1, each of which has just one negative Laurent term (2k+1)!*z^(-2k-2). These are exact elliptic derivatives with zero periods. The remaining elliptic function is a*p+b. Thus half its period is b*omega-a*eta, obtained without the source power-period recurrence or the IBP expression.

More explicitly, if S=(p^(m-1))^2, then a=[z^-2]S and

    b=[z^0]S - sum_(k>=1) [z^(-2k-2)]S * c_(k+1)/(2k+1).

The sum is finite for each m. Computing the needed Laurent coefficients exactly gives both claimed coefficients for m=1..16 and verifies both full supports for m=2..16. Evidence: checker-evidence.json. Resource controls: hard512MiB address space,40CPU seconds,50second alarm,55second external timeout; BLAS/OMP/MKL threads1. Exit0, all checks PASS. Truncation includes coefficients through c17, more than needed for the constant of the m16 square; differentiation and negative exponents are explicit. These finite diagnostics do not prove the analytic theorem or establish novelty. No Lean was written or run.

## Substantive eligibility: strongest cases both ways

**Best EXCLUDE case.** The classical input really does concern the same Weierstrass invariants and sigma underlying the source's wp; it is closer than an arbitrary generic inequality. The product decomposition is standard elliptic partial fractions (Hermite), the period integration uses only quasiperiodicity, and extracting a Taylor coefficient followed by source equation (23) is mechanical once that product is chosen. The positive Laurent recurrence is already printed immediately next to the source's Bernoulli discussion. An expert could regard finding and assembling these facts as routine. No explicit earlier publication announcing this conjecture's solution is required for a routine-corollary exclusion. This is the strongest plausible objection; the proof's correctness does not defeat it.

**Best substantive case, adopted here.** The actual closest body inspected, Theorem37, stops at sigma's parameter PDE. It gives no identity for these squared-derivative periods or their correlation generating function. Source Propositions4,6,7 and8 give power periods, signed corrections, and Halphen principal parts; none identifies Bhat with the Bernoulli–Hurwitz coefficient or Ahat with its positive invariant derivative. The new content is precisely simultaneous identification of both period components, including the eta*t*p' term and constant normalization. It is not a choice of numerical parameter in the heat theorem. Invoking the generic Hermite method does not itself document a published theorem already carrying that identification.

I read the root gamma investment decision and the full perspective re-adjudication, the Hoggatt root decision, and the An–Djokovic explicit corollary bridge. Hoggatt has the exact separated kernel theorem plus the source induction; An–Djokovic has a published evaluation of the relevant monomial pairing followed by terminal descent/binomial specialization. Here a published evaluation of the period correlation or equivalent derivative-square generating function would supply the analogous bridge. None has been established by the cited classical body. The gamma precedent treats the exact object-to-tool identification as substantive even though the final tool is classical. Applying that calibration consistently favors preserving this identification as substantive candidate content. Every classical identity, generic partial-fraction method, IBP, and recurrence remains uncredited separately.

This is not a claim that CFT Ward identities, elliptic integral tables, Halphen's original volumes, or modular-form derivative literature contain no equivalent result. Those genres remain a specific residual risk. The correct response to that risk is a bounded antecedent/source HOLD, not an unsupported assertion of a concrete same-object subsumer. An open-source label and an unsuccessful search do not establish novelty; I have not used either as the positive reason for substantive eligibility.

## Sources and bounded antecedent investigation

Read actual primary arXiv body §4 power periods, §5 Definition(21), Propositions6–8, §7 Conjectures1–2; actual Buchstaber–Bunkova §8.4 theorem body; actual published companion Theorems3.1–3.3,4.1,5.1 and §6. The companion concerns odd trace polynomials in spin s; §6 expressly distinguishes the even complete-integral construction. It supplies no same-object positivity theorem in the portions read. Chronology: source arXiv August2005; companion published2008; heat reference arXiv April2012, explicitly labels its input Weierstrass's theorem. No exact 19th-century printing was authenticated in this review.

Live primary DLMF23.10(i) was read: equations23.10.1–6 are addition identities; none states the period-product coefficient theorem. DLMF23.2 supports periodicity/quasiperiodicity, and23.8 was fetched as a Fourier-series antecedent screen, not as a proved non-subsumption claim. Searches used elliptic Bernoulli positivity/generating functions and Weierstrass period-product/correlation terms. Search hits included another elliptic Bernoulli function family (polylogarithmic/Jacobi forms), general elliptic decompositions, and integral representations, but no obtained body carrying this endpoint. A promising MPI torus Ward-identity PDF returned403; stopped without bypass. Its search snippet is not treated as a body read or clearance. Cached handbook.pdf is truncated at16MB and unusable; not relied on.

A new legitimate public route succeeded: https://api.figshare.com/v2/articles/9383633 lists 05-43.pdf; its advertised public download https://ndownloader.figshare.com/files/16995383 returned294521bytes, SHA25694b33c446913b2cc227a9530ee300357d07072888602f8ebd451d70ab1c2baa6. I extracted its text, read the relevant sections and visually inspected p17 containing Conjecture2. Repository published_date is2005-11-10, earlier than the March2006 revision/acceptance dates recorded by the candidate. Its target statement remains a conjecture and the literal definition remains the same. The body lacks publisher VoR identification. Therefore it is useful independent manuscript evidence, **not a certification of the 2006 published body or an accepted-version equivalence**. The earlier Oxford403 and institutional202/empty failures are preserved; no repeat challenge or access bypass was attempted. Published-source HOLD remains.

## Registry scope, chronology, and integrity

Fresh heads obtained at the UTC times in new-sources/http.json: Omega-dev31c2fcf8d598e1a26f6ea185f08b50a47ac9dd54; main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM8729eab98bafe409b66c5e39253bf56569a62327; Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a. The last four match the candidate. The new dev comparison from6e842c9a returns3commits and217file changes, all with returned patches. No elliptic/Bernoulli/Grosset/Veselov/Weierstrass/Faulhaber keyword occurs in those patches. Changes concern digestion metadata and strict real joint incidence support. Commit times are11:02:07,12:07:21,12:13:38UTC; chronology is recorded exactly, not presumed monotonic from ancestry. This updates the candidate's earlier19commit/8file delta only. It is not whole-dev coverage or full semantic proof-body coverage of opaque atom files; API patches may omit portions. The inherited D5/Problems and complete other-registry subtree screens remain bounded evidence, not a fresh exhaustive audit. The cached closest Omega coth and elliptic-tail claim bodies are different remainder questions. Accept pinned OpenAI theorems as true; no upstream-truth audit performed.

All49 frozen candidate files matched before copying. Work and checking used my own inputs copy. Original34-entry manifest is separately checked against originals; final freeze and manifest results are recorded after the review. No original/shared/other-lane edits, git operations, child agents, browser tabs, posting or account operations. The report creates no formal certificate or acceptance artifact. Remaining decisive work: authenticate/compare the published source and investigate a genuinely same-object period-product antecedent; do not spend on formalization merely on the strength of this ordinary-proof PASS.
