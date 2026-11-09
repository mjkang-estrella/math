# Independent preliminary review: Auconi information-response claim

Decision: SOURCE PASS; MATH PASS; SUBSTANTIVE: recommend routine-adaptation exclusion; NOVELTY: bounded, not cleared; FORMAL-FEASIBILITY: conditional interfaces only. This is a recommendation to root, not acceptance, a shared-ledger exclusion, or a discovery credit. Counts remain 9 additional / 39 total / next 40. The scout screened twelve statement rows in SIX families, not twelve distinct families. No Lean or manuscript was written.

## SOURCE

I independently read the frozen actual primary bodies, re-extracted with pdftotext from the copied PDFs; I did not run or reuse the candidate checker. Primary targets:

* Auconi, https://arxiv.org/pdf/2308.09638v2 : main p1 Eq(1)–(2), main p2 proofs/applications, supplement Sections I–II (PDF pp4–5), Section IV (small-noise proof), Section V (variational argument), and remaining examples/numerical scope. PDF SHA256 6a55293a4ba99869c26b0d984b0454a333d56934a559abf251326c812ffadf58.
* Angulo–Ruiz-Medina, https://arxiv.org/pdf/2212.12209v1 : Section 2.1 Eq(1), Section 3.1 Eq(9), Lemma 1 argument, and Theorem 1 with complete proof, pp10–11. PDF SHA256 a4ec930b6b98000557e21ffdce6d84ece0e1b540fc6cd80d61c738902be8e361.
* Barnes–Özgür, https://arxiv.org/pdf/2102.05802v2 : definition, regularity (i)–(iii), Theorem 1 and proof pp2–3. PDF SHA256 d63798fbb2068964ad7006f2124f8f36ce43d56d2f3252e5b9b8c2d2b6e2b646.

Auconi's main p1 explicitly introduces smooth probability densities, a fixed channel p(y|x), and q(x)=p(x-epsilon). Eq(1) is J gamma = E_Y[(E[s(X)|Y])²], s=partial_x log p(x), J=E s². This is the INPUT marginal score, not partial_x log p(x|y), partial_x log p(y|x), or a joint score. Supplement I spells out the conditional brackets; supplement II explicitly says arbitrary smooth channel and translates only the input. Its Eq(6) has D[q_Y||p_Y]/D[q_X||p_X]. Natural logarithms are used. There is one real input and one real output; a 3-dimensional dynamical extension is only discussed as future work. No centering, symmetry, Gaussian-input restriction, additive channel, stationarity/detailed balance, or dynamical embedding is imposed on main Eq(2). Boundary and differentiation assumptions implicit in its integrations by parts must hold; they do here.

The main p2 Gaussian-input thermodynamic application is a restricted application, and its Gaussian/small-noise channel argument concerns a large-information asymptotic. Neither narrows the universal conjecture. The supplement's Gaussian stationary-point calculation explicitly warns that stationarity does not imply a global maximum or establish the conjecture. Its numerical family Eq(38) is a sampled evidence family, not the domain of Eq(2). I do not treat that computation, or the proposed witness, as a refutation of the restricted Gaussian results. If mean zero were desired, translating the witness by its finite mean preserves the calculations, but no such repair is needed for the literal target.

## MATH

All-real calculation, independently checked. Put t=e^x/(1+e^x). This is a smooth increasing bijection R to (0,1), t'=t(1-t), p=2t(1-t)² and p(x)dx=2(1-t)dt. Thus p integrates exactly to one. Differentiating log p gives s=1-3t, so -2<s<1. For every integer k>=0,

    M_k = integral_0^1 2(1-t)(1-3t)^k dt
        = sum_{j=0}^k binom(k,j)(-3)^j 2/((j+1)(j+2)).

This proves, by exact integration rather than quadrature, M0=1, M1=0, M2=1/2, M3=-1/5, M4=3/5. In particular J=1/2>0. Also s'=-3t(1-t) and E s'=-1/2. The independent Fraction checker recomputes these polynomial integrals directly.

For a=1/100, s(x)s(y) lies in (-2,4), hence 49/50 < 1+a s(x)s(y) < 26/25. (The weaker |s(x)s(y)|<4 is used only for the series bound.) P=p(x)p(y)(1+a s(x)s(y)) is an everywhere positive C-infinity Lebesgue density. Integrating x or y using M1=0 proves BOTH marginals equal p and total mass one. K(y|x)=p(y)(1+a s(x)s(y)) is normalized for every real x. P is not a marginal density; the conditional p(x|y) is P/p(y). Consequently

    E[s(X)|Y=y] = a M2 s(y),
    E_Y[(E[s(X)|Y])²] = a² M2³ = 1/80000,
    gamma = a² M2² = 1/40000.

All conditional expectations here are under P, while the entropy expansion below is under the product measure p tensor p. Confusing these measures would change the moments.

Let X0,Y0 be independent with density p, z=a s(X0)s(Y0), r=4a=1/25. Then |z|<=r, E0 z=0 and E0 z^k=a^k M_k². The ordinary Taylor identity

    (1+z)log(1+z)=z+sum_{k>=2} (-1)^k z^k/[k(k-1)]

converges absolutely and uniformly on [-r,r]. The majorant sum r^k/[k(k-1)] is summable; expectation can be interchanged with the series. For the tail beginning at k=4, pointwise absolute value is bounded by |z|^4/[12(1-r)]. Integrating gives

    I = E0[(1+z)log(1+z)]
      <= a²/8 - a³/150 + (9a^4/25)/(12(1-4a))
       = a²/8 - a³/150 + 1/3200000000.

The cubic term is negative because E0 z³=a³ M3²=a³/25>0 and the series coefficient is -1/6. The fourth-moment remainder uses M4²=9/25, not M4 and not a fourth moment under P. Thus

    gamma-2I >= 61/4800000000 > 0.

For nonnegativity, f(z)=(1+z)log(1+z)-z has f(0)=f'(0)=0 and f''(z)=1/(1+z)>0; E0 z=0 gives I>=0 directly. Indeed I>0 since z is nonzero on a set of positive measure. All information integrals are finite because the likelihood ratio is in [49/50,26/25]. Finally e^(-u)>=1-u yields 1-e^(-2I)<=2I<gamma. The claimed rational gap is a bound on gamma-2I and therefore also a strict lower bound on gamma-(1-e^(-2I)). No finite numerical experiment enters this proof.

Independent translation check. Set q_h(x)=p(x-h), hold K fixed, and c(h)=integral p(x-h)s(x)dx. Exactly,

    q_h^Y(y)=p(y)(1+a c(h)s(y)), c(0)=0,
    c'(0)=-integral p'(x)s(x)dx=-J.

Since |s|<=2, p(x-h)<=e^(2|h|)p(x), by integrating the bounded derivative of log p. Each derivative p^(k)/p needed here is bounded: t'=t(1-t) and s polynomial in t make this immediate up to order three. On |h|<=H, these derivatives times bounded s have one integrable envelope C_H p(x). Dominated differentiation gives c(h)=-Jh+O(h²). The same entropy series, now with z_h=a c(h)s(y), gives D[q_h^Y||p]=a² J³ h²/2+O(|h|³)=h²/160000+O(|h|³).

With U distributed according to p,

    D[q_h||p]=E[log p(U)-log p(U+h)]
             =-h M1 - h² E s'/2 + O(|h|³)
             =J h²/2+O(|h|³)=h²/4+O(|h|³).

The third derivative of log p is bounded, so Taylor's integrated remainder is uniformly controlled. The tails satisfy p(x)<=2e^x for x<=0 and p(x)<=2e^(-2x) for x>=0. Thus p, p', p'' vanish at both ends, p s vanishes, all polynomial moments and differential entropy are finite, and integrating (p s)' proves E s'=-J. This establishes the boundary terms, signs, two-sided h limit, positive denominator near zero, and ratio a²J² independently of the source's formal expansion. Translating the joint or allowing K to depend on h would be a different experiment.

## SUBSTANTIVE

Strongest objection, and my recommendation: exclude from discovery credit as a complete routine classical adaptation. This does NOT mean an arbitrary use of classical methods excludes new work. The specific full bridge is as follows.

For ANY bounded centered kernel f with v=E f²>0, a positive rank-one joint p(x)p(y)(1+a f(x)f(y)) has exact score-response

    gamma_f=a² (E[s f])² v/J,
    2I_f=a² v² - a³(E f³)²/3 + O(a^4).

Cauchy–Schwarz gives (E[s f])²<=Jv. Therefore the quadratic obstruction disappears precisely when f is proportional to the input score (modulo null sets). Taking f=s is the direct equality choice. If E s³ is nonzero, the cubic entropy term then automatically supplies the desired strict sign for small positive a. Constructing a bounded skew score is achieved by a logistic transform of a Beta(1,2) density, giving s=1-3t and elementary polynomial moments. Choosing a rational a and bounding the fourth tail supplies an explicit certificate without changing the mechanism. The sign, source response normalization, admissible positivity interval and all remainder conditions are established above; there is no leftover nonlinear inequality, global optimization or existence theorem in this bridge.

This is a target-specific derivation of the entire mechanism, not exclusion by shortness. The steps supplied by the candidate beyond the classical framework are score alignment, a nonsymmetric bounded-score choice, and rational instantiation of the standard expansion. In this reviewer's judgment those steps are routine once the source's conditional-score formula and rank-one model are placed together. The argument does expose a genuine failure of the intended universal statement, rather than an endpoint, normalization or weakened-domain loophole. That merits retaining it as mathematically valid research, but does not compel substantive discovery credit under this campaign's stricter exclusion of routine adaptations. Root alone adjudicates; this lane does not edit the ledger. If root finds the equality-case score alignment sufficiently substantive, the math/source gates survive, while novelty and formal gates remain open.

Actual source comparison, with important limits: Angulo–Ruiz-Medina Eq(1) uses a complete orthonormal basis with coefficients gamma(distance)^k in a homogeneous isotropic random field. Eq(9) is the exact joint-relative-to-product entropy integral; the following argument Taylor-expands its logarithm. Their Theorem 1 concerns finite-state subordinations of rank m and long-distance O(distance^(-m rho)) behavior under Assumption I. Its proof uses Jensen, basis moments, geometric-series bounds, and upper/lower comparisons. It contains no input-translation score, no source gamma response, no cubic sign certificate, and no Auconi counterexample. In particular, one cannot literally set all k>=2 coefficients to zero while keeping gamma^1 nonzero in that displayed restricted random-field family. The bivariate rank-one construction is the classical adaptation, not a literal specialization of their Theorem 1. I do not rely on that theorem's proof to justify any analytic step here, or claim that its stated asymptotic alone subsumes this target. I read the actual complete proof, including its lower-bound paragraph, rather than treating its abstract as a resolution.

Barnes–Özgür Theorem 1 gives Tr I_Y<=2N² I(X;Y) for every unit-direction score N-sub-Gaussian, under differentiability of sqrt density, finite continuous input Fisher information, and channel square-integrability. The proof lifts to independent products, uses the conditional-score identity, splits typical and atypical likelihood-ratio events, bounds a squared-score exponential moment and a fourth moment, then takes B to infinity and lambda to one. This is an information bound with a proxy N², not the variance J. Here the location-parameter score is -s; the sign flip changes its third moment but not its variance or squared conditional expectation. A variance-tight proxy N²=J is impossible: boundedness makes log E exp(t s)=Jt²/2+M3 t³/6+O(t^4); one sign of t makes the cubic positive. A valid proxy is N²=9/4 from the bounded interval of length three (Hoeffding's bound), leaving ample slack. The location family and channel satisfy their regularity conditions by the domination above and K(y|x)²<= (26/25)² p(y)². Thus their theorem is neither refuted nor a disguised version of the claimed universal inequality. Auconi's own discussion correctly uses J<=b², not equality.

## NOVELTY

No exact previous public resolution was located. I do not claim one exists, or substitute a classical formula for a dated public resolution. Chronology from the fresh primary arXiv API on 2026-10-30: Barnes–Özgür first 2021-02-11, v2 updated 2021-07-08; Angulo–Ruiz-Medina first/latest v1 2022-12-23; Auconi first 2023-08-18, latest v2 updated 2023-09-20. Auconi's printed title-page date is September 21, 2023, distinct from the arXiv update. All three precede this campaign. The current entries supply no journal_ref or DOI; this is NOT proof that no published versions exist. Auconi's own reference identifies Barnes–Özgür as ISIT 2021 pp2179–2184. I have not independently compared the published proceedings body to v2.

Fresh lawful checks are saved in evidence/current-access.json and current-summary.json: specific-id latest versions, 30-result author query (14 returned), 20-result information-response phrase query, and a targeted all:2308.09638 query returning only the target entry. The broad phrase query is noisy and date-limited; it is not absence evidence. These are primary arXiv metadata checks, not complete citation or proof-registry searches. A later author paper, 2403.16631v1, was retrieved, frozen before extraction, and screened at its actual setup and for target/score/conjecture terminology; its setup concerns Fokker–Planck steady currents and relaxation, not a universal fixed-channel refutation. This is only a targeted body screen, not a theorem-by-theorem clearance. Another later author PDF, 2606.14329v2, reached the 8,000,000-byte retrieval bound and could not be parsed; the prefix, error and hashes are preserved and the body remains UNREAD. No body-based clearance is claimed for it.

Current GitHub-backed public-proof registry heads and old inaccessible historical intervals remain unverified. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not retried. No proxy, TLS disabling or browser bypass was used. No 403/429/challenge occurred in my permitted requests. No exhaustive citing-body, publisher, subscription database or worldwide-priority search is claimed. The routine-adaptation recommendation is independent of these unresolved priority limits. A positive acceptance recommendation would require stronger current-prior evidence.

## FORMAL-FEASIBILITY

No Lean or paper work authorized or attempted. If root overrides the substantive recommendation, the useful interfaces are: logistic substitution for all-real density moments; smoothness/score/tail bounds; product density and fixed normalized kernel; conditional-expectation identification; exact response quotient; integrability and uniform entropy-series remainder; exact rational strict gap; KL nonnegativity and exponential comparison. Alternatively add the dominated-translation derivative and second-order KL interfaces above. A formal endpoint must refer to the actual density/channel integrals and the source response, not assume the moment/entropy bridge as unproved hypotheses. The rational checker is supporting evidence only and does not certify those analytic interfaces. No build feasibility or effort estimate has been established.

## Provenance, failures and integrity

Read ancestor/batch AGENTS.md and administrative ledger/prior-context snapshots. All mutations are inside this lane. No shared/git/public/browser/MathDB edits, no children. All Python, pdftotext children, retrieval, writes and hashing ran through the specified helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1, fixed AS and sampled group RSS 512MiB / CPU210s / wall230s, no raises. Independent checker passed under the guard (sampled group RSS 9,768,960 bytes; wall about .04s). Sampling is not a proof of absence of between-sample peaks.

freeze.json records selected scientific originals, copies, sizes and SHA256 before first scientific reading in this lane. Only selected objects were copied, with no recursive historical duplication. New live bodies were stored and hash-bound before extraction; extra-access freeze evidence records that separately. Administrative files are snapshots, not immutable scientific assertions. The inherited r221 report admits its original r216/r217 scientific-report reading preceded freezing; that caveat is preserved verbatim in frozen/FAILURES.md and is not repaired retroactively by this lane's clean freeze order. Candidate checker was not read or reused.

Failures retained: the initial native path search was overbroad, produced a truncated inventory and no usable scientific body read; subsequent reads were bounded and lane-specific. The first combined body output was truncated; the named theorem/translation/proof sections were read again in bounded portions. Candidate's failed loose fourth-moment shortcut remains in its frozen proof. My later-author PDF prefix was truncated and pdftotext failed; it is not a frozen complete source body. No cap was raised or retry used to conceal that failure. Exact retrieval statuses/hashes and failure exception are in evidence/additional-access-freeze.json.

Final integrity uses before/after original-and-copy hashes in before-after.json. manifest.json covers the final payload and excludes itself and verification-receipt.json. A separate guarded verification invocation verifies those payload hashes, the scientific originals/copies and the independent checker after all payload writes. The receipt records that result. No acceptance or count change follows from its success.
