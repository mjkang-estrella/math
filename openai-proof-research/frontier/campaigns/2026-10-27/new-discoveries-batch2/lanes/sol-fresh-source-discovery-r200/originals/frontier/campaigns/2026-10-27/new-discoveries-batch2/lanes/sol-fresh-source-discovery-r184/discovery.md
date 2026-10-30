# r184: fresh analytic screening; zero complete resolutions

Counts remain 9 additional / 39 total, next 40. Research only. Root owns review, investment and acceptance.

## Early identity screen and bounded breadth

Before selecting targets, rebuilt the qualified original SUMMARY/discovery/PROOF/review/DECISION screen from r181/r180/r179/r178/r170 receipts, retaining all inherited originals, including r111–113. `history-receipt.json` records 2,523 files, 11 changed/new and zero missing. No echo was excluded; conservative duplicate copies remain. Every hash is of the actual bytes, not a path-presence inference. `early-screen.json`, `exact-early-screen.json` and `legendre-screen.json` record DOI, arXiv, title phrase, author and statement aliases. The only narrow Cheeger-author hit is an unrelated Muratov–Novaga–Ruffini charged-drop review; no target match. Legendre-specific screen has zero hits. This establishes bounded project freshness, not literature novelty.

Broad reconnaissance included entropy/log-concavity, Bessel monotonicity, Mittag–Leffler modulus, Robin torsional rigidity, Cheeger torsion, and Gauss–Legendre inequalities. Existing credited Mittag–Leffler/gamma-level science was recognized through original candidate/review counterparts in early-screen.json; not selected. Poisson/Wasserstein, Gaussian Radon, Karp–Sitnik, snake, one-bit/means, DSBS/pendulum and active arithmetic/structural lanes were excluded by assignment, not claimed newly screened questions. The 2026 negative-Robin result explicitly resolves the higher-dimensional extension in its own theorem; it is reconnaissance only, not a fresh question. The source-pool JSON failed to fit fixed memory; no cap increase. The two genuinely fresh statements below were investigated after the screen. There is no quota filled by three retired targets.

## Strongest fresh target: published uniform circle conjecture

Óscar López Pouso and Javier Segura, *Uniform relations between the Gauss–Legendre nodes and weights*, Journal of Inequalities and Applications (2025) 40, DOI 10.1186/s13660-025-03283-w, Conjecture 1, journal pp6–8. Actual published PDF and latest arXiv:2305.19128v3 both obtained and read. arXiv versions: 30 May 2023, 27 January 2024, 22 January 2025; journal received29August2024/accepted10March2025/published20March2025. No later arXiv version appears on the live abs page.

For every integer n>=1, let x_1<...<x_n be the zeros of the Legendre polynomial P_n normalized by P_n(1)=1, and let w_i=2/((1-x_i^2)P_n'(x_i)^2). Put k=n+1/2 and y_i=k w_i/pi. The literal full assertion is

    0 < 1-x_i^2-y_i^2 < 1/(4 k^2), for every i=1,...,n.

This implies uniform asymptotic proximity to the circle. No deletion of extreme nodes, no fixed-index restriction, no large-n-only substitution, no central-node ratio convention, and no Bessel-only helper is proposed as a resolution.

The source gives separate bulk and fixed-boundary-index asymptotics and a Bessel limiting coefficient tending to1/4, but explicitly leaves monotonicity and uniform control unproved. Its Appendix C already proves the elementary Sonin zero-derivative monotonicity used below. Repeating that lemma would be routine, not substantive credit.

### Exact universal reduction

Write x=cos(theta), s=sin(theta)>0, u(theta)=sqrt(s)P_n(cos(theta)), and A=k^2+1/(4s^2). Direct differentiation and the Legendre equation give u''+Au=0. At a zero theta_i, put d_i=u'(theta_i)^2=s_i^3 P_n'(x_i)^2>0. Then w_i=2s_i/d_i and

    1-x_i^2-y_i^2=s_i^2(1-4k^2/(pi^2 d_i^2)).

Thus the lower strict deficit is exactly d_i>2k/pi. When 4k^2s_i^2>1 the upper deficit is exactly

    d_i < (2k/pi)/sqrt(1-1/(4k^2s_i^2)).

When 4k^2s_i^2<=1, the upper deficit follows immediately from the displayed formula and y_i>0, so this division is unnecessary. These are equivalences, not a proof of either required slope estimate.

On (0,pi/2), A'<0. The classical identities

    E=u'^2+Au^2, E'=A'u^2;
    F=u^2+u'^2/A, F'=-A'u'^2/A^2

give E(theta_i)>=E(pi/2) and d_i<=A(theta_i)E(pi/2)/A(pi/2). Reflection handles the other half. For n even, E(pi/2)=(k^2+1/4)P_n(0)^2; for n odd it is P_n'(0)^2. These values have exact central-binomial formulas. Establishing their sharp Wallis inequalities would be needed for the first strict estimate; those inequalities are not silently assumed proved here.

The raw upper envelope is too weak: its leading s-dependent relative correction is 1/(4k^2s^2), whereas the required bound has 1/(8k^2s^2). `checks.py` verifies an exact rational method countermodel (not actual Legendre data): for k=3, s^2=1/4 and hypothetical normalized center73/72, the envelope is365/333 and its square exceeds9/8, the squared target. Consequently the two Sonin monotonicities alone, even with fairly sharp center normalization, cannot close the source quantifier.

Plausible universal route: build a higher-order Sonin comparison adapted to the explicit potential A and control its signed remainder uniformly through the boundary layer, calibrated by the exact center data. It would have to prove the displayed slope bound at all actual zeros, with strictness, rather than only its Bessel limit. The positive potential and explicit derivative make this concrete, but no sign-controlled corrected functional was obtained. Strongest objection: the sharp1/4 deficit is approached in the bulk; a comparison with a larger constant cannot be repaired by finite checks. No complete ordinary proof, counterexample, or candidate PROOF.md is claimed.

### Primary/classical and companion comparison

Gautschi, *The circle theorem and related theorems for Gauss-type quadrature rules*, ETNA25(2006)129–137, actual author PDF read, §2 Theorem1 and proof: Nevai Christoffel asymptotics are uniform on a fixed compact interval Delta inside(-1,1), with n normalization. That proof does not control all extreme nodes or give this finite-n strict defect. It supplies no complete bridge.

López Pouso–Segura, *Analysis of difference schemes for the Fokker–Planck angular diffusion operator*, actual latest arXiv:2308.08950v1, §4 pp6–7 read: spacing/weight propositions are established, but additional uniform node/weight properties are explicitly described as lacking complete proofs. This is not a proof of Conjecture1. Its published2025 VoR was not obtained; retain that material body gap. The current Segura publication list also identifies a 2025 Morel follow-up and2026 quadrature algorithms; listings do not clear their bodies. Förster–Petras1990 ultraspherical weight estimates is a particularly material unread classical comparison: bounded AMS retrieval did not yield saved PDF bytes. No subsumption judgment is asserted for it.

## Secondary fresh target: Cheeger–Kohler–Jobin

Ilaria Lucardesi, Dario Mazzoleni, Berardo Ruffini, *On a Cheeger–Kohler–Jobin inequality*, latest arXiv:1806.01549v3 (6March2023), actual cvgmt5932 body Conjecture1.2 and §§5–6. For every open bounded convex Omega in R^N and every ball B,

    T_2(Omega)^(1/(N+2)) h_1(Omega) >= T_2(B)^(1/(N+2)) h_1(B),

with equality iff Omega is a ball. The institutional publication record identifies DOI10.1007/978-981-97-6984-1_3, pp25–47, with2024 imprint; cvgmt metadata says2025. Exact journal/chapter equivalence remains HOLD: its apparent AAM URL returned a login HTML response, preserved under the requested PDF filename. No authentication attempted.

An older same-author public body cvgmt3886 *A Cheeger–Kohler–Jobin inequality* claims the full result without convexity. Its Theorem1.1 proof Step1 compares volumes of equal-height level sets and integrates perimeter bounds. The latest body §5 specifically says the rearrangement changes heights through psi(t), cannot be taken as identity, and preserves only a conditional support inclusion Hypothesis5.6, B-sharp subset B_(Omega,u). Thus the stale claimed theorem is NOT certified as a valid public resolution of the later conjecture. No claim of a new refutation of that old proof is made. We preserve the chronology and exact mechanism rather than retiring on its abstract.

The plausible source route is an r-down-to1 limit of Kohler–Jobin rearrangements. It remains precisely stuck at Hypothesis5.6, and even that hypothesis supplies the inequality, not equality rigidity (latest Remark1.5). This is source-supplied machinery, no decisive new universal route found; not recommended for investment. It is a fresh unresolved statement here, not an old reopened lane.

## Prior and access limits

Searches were public read-only search and direct primary HTTP; no browser. Inherited166 adverse-access inventories inspected first. No denied GitHub/raw/codeload/patch, ScienceDirect, Google challenges, IEEE, OpenReview, d-nb, or arXiv search routes retried. Exact successful URLs, final redirects, UTC, sizes and SHA256 are in http.jsonl. Wrong guessed companion v3/v2 URLs gave404 before correcting to the actual abs-page v1; these failures are preserved and not concealed. The AMS response exceeded the12MB read bound (empty AssertionError in the original receipt); no bytes saved and no retry. The AAM is an HTML login body, not PDF authentication.

`registry-screen.json` hashes and screens11 cached path inventories. Matching Legendre names refer to arithmetic recurrences/characters; quadrature names are generic/in other fields. No matching uniform-node statement is visible, but absence of a title/path match is NOT clearance. Current registry heads and inaccessible bodies remain HOLD; historical caps and missing merge trees stay PARKED, with no reconstruction loop. No significant formal or acceptance investment follows.

Result: one sustained strongest route and one secondary fresh unresolved statement, zero complete full-scope resolutions. No Lean, manuscript, shared edits or count change.
