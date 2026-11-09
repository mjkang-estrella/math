# r57: fresh analytic source screen, excluded classical reduction; credit 0

Solo research on 2026-10-29, approximately 15:41–15:51 UTC. Only this lane was created/edited. Counts observed: 6 additional / 36 total; root owns acceptance. No nomination, PROOF.md, Lean investment or paper. The full-scope ordinary implication below is preserved as an **excluded classical corollary**, not promoted into a discovery. It is not a numerical claim or an unresolved claim disguised as a solution.

## Context and source selection

Read ancestor and campaign AGENTS, current NEXT, ledger and prior-campaign-context, r54/r55 summaries and r55 discovery/current registry warnings. Parsed the complete JSON inventories; hashes in context-screen.json. Read the catalogue opening and immutable upstream revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No credited family is recounted. Active polyomino, finite/algebraic r56, Nuttall, p-Seidel, beta median, Mathieu, Wright and user-listed exhausted targets were avoided. A Tsallis search lead was immediately excluded upon reading the earlier r5 SUMMARY: it was not a fresh question or a pursued fourth candidate.

Three actual source assertions were screened, from two new source papers:

1. **Rohman ellipse bound**, Jurnal Ilmiah Matematika dan Pendidikan Matematika17(1)(June2025)11–34, DOI10.20884/1.jmp.2025.17.1.15684. Read actual PDF p28 §1.2.2 (render claim.png) and related pp21,24–29 text. The displayed proposed “greatest lower bound” is L*=π((a+b)/2+sqrt((a²+b²)/2)), across a≥b≥0. Its lower-bound clause is classical; its unrestricted “greatest” clause has no specified competitor class and is false under the ordinary pointwise meaning. This is excluded, not nominated as a wording refutation. Actual source journal PDF obtained from canonical jos.unsoed hostname after obsolete indexed hostname DNS failure; no bypass.
2. **KVZ preprint log-concavity**, Karp–Vishnyakova–Zhang arXiv2408.01755v2, Conjecture1 p12, retained in saved March2025 author manuscript: for ν1≥ν2>0 and 0<a1≤a2, log(Iν1(a1x)/Iν2(a2x)) is concave for every x>0. Publicly refuted before this lane. Read actual current Problems file and Result.md theorem body. Registry witness ν1=ν2=1/10, a1=1,a2=2 at x=3/2,9/2,15/2; dated public path history commit c27ba49982568b4465a7808f7a503faf0b61976b, 2026-10-25T08:06:22Z. Reproduced exact infinite-series enclosure, excluded. The published Results Math80:112 body actually **omits** this log-concavity conjecture: compare author PDF p12 to published PDF p18. Do not attribute this clause to the published ending.
3. **Selected serious full-scope investigation: KVZ general-order unimodality.** Same author's preprint Conjecture1 and the actual published Results Math80:112(2025), DOI10.1007/s00025-025-02431-4, final paragraph of §4, p18 of27. For **all real ν1≥ν2>−1 and all 0<a1≤a2**, x↦Iν1(a1x)/Iν2(a2x) is unimodal on (0,∞). Source unused b≥0 is harmless. Source definition p6 includes monotone and constant functions, and both peak and valley single turns. Source Theorem4.3 proves the Q-function transform assertion for even integer order differences; its preceding argument proves the corresponding Bessel claim. It does not supply the general-order argument below. General-order statement is distinct from both Nuttall Riemann-Phi work and the prior Karp incomplete-beta family.

## Ellipse classical exclusion, with endpoints and equality

Put h=((a−b)/(a+b))² for a+b>0. Villarino arXiv:math/0506384v1, §4 Theorem3 (Ivory identity) and Corollary1, gives

    L/[π(a+b)] = sum_(n≥0) binom(1/2,n)² h^n ≥ 1+h/4.

This is a convergent identity also at h=1, not an extrapolated truncation. Meanwhile

    L*/[π(a+b)] = (1+sqrt(1+h))/2 ≤ 1+h/4,

since sqrt(1+h)≤1+h/2. Both inequalities are strict when h>0 (the n2 Ivory term is positive, and the square-root tangent is strict). Thus the actual lower-bound inequality holds for all a≥b≥0, including b=0, with equality exactly a=b; (0,0) handled directly. It is strictly dominated away from the circle by the classical lower bound π(a+b)(1+h/4). No proof of a meaningful maximality assertion is obtained, and no discovery credit is justified. The paper also discusses the already classical Ramanujan lower approximation. Neither failure of maximality terminology nor an endpoint repair is eligible.

## Sustained general-order mechanism: exact Wronskian, not a sampled grid

Let f(x)=I_u(ax), g(x)=I_v(bx), with u≥v>−1, 0<a≤b and x>0. The positive-term defining Bessel series gives f,g>0 and smoothness on (0,∞); ratio test gives locally uniform convergence of the series and every differentiated series on compact subsets there. Termwise differentiation gives

    f'' + f'/x − (a²+u²/x²)f=0,
    g'' + g'/x − (b²+v²/x²)g=0.

This step is valid for negative noninteger orders >−1 as well: factor x^u times an entire power series in x², and differentiate on a positive compact interval. No positivity of f' or g' is needed.

Define

    W=x(f'g−fg'),   A=u²−v²,   B=b²−a²≥0.

Direct differentiation and substitution cancel the first-derivative terms:

    W'=(A/x−Bx)fg,
    (f/g)'=W/(xg²).

The nontrivial issue is **not** to infer one zero of W merely from one turn of W': a function increasing then decreasing could cross twice. Endpoint information removes the first crossing.

Write δ=u−v≥0, s=u+v. With positive C=(a/2)^u(b/2)^v/[Γ(u+1)Γ(v+1)], the source series yields

    W=C x^s [δ+O(x²)]                    if δ>0.

Hence W>0 on a punctured interval at zero, even when s<0 and W diverges. When δ=0, A=0 and

    W=C x^(2v+2) [(a²−b²)/(2(v+1))+O(x²)].

Since v>−1, W tends to0 in this case. These are convergent local expansions, not large-argument asymptotic assumptions.

Case δ=0: W'=−Bxfg≤0. If B>0 then W is strictly decreasing from limit0 and W<0 for every x>0; ratio strictly decreasing. If B=0 the two functions coincide and ratio=1.

Case δ>0,A≤0: W'≤0. Unless A=B=0 it is strictly negative everywhere. A strictly decreasing W, initially positive, is either positive throughout or crosses once from positive to negative. When A=B=0, W is constant and positive (s=0, local expansion gives W=Cδ>0). Thus the ratio is increasing or first increasing then decreasing.

Case δ>0,A>0,B=0: W'>0 everywhere and initial W>0, hence W>0 everywhere and ratio strictly increasing.

Case δ>0,A>0,B>0: let t=sqrt(A/B)>0. W'>0 on (0,t), W'<0 on (t,∞). Initial W>0 implies W>0 on (0,t], after which a strictly decreasing W can cross zero at most once. Again ratio is increasing or first increasing then decreasing. A zero at t cannot occur because W(t)>0.

These cases exhaust **all** source orders and scales, including u+v<0, u+v=0, equal orders and equal scales. By the derivative sign and mean value theorem, the full source unimodality conclusion follows. No zero is asserted to exist when the argument only proves at most one. Constancy is possible exactly when u=v and a=b: a constant ratio would force W≡0, hence A−Bx²≡0, so B=A=0; distinct orders with u=−v give W=Cδ>0 and cannot be constant.

A second route via the Riccati variables U=x f'/f, V=x g'/g gives

    x(U−V)'=A−Bx²−(U+V)(U−V).

At a zero of U−V its derivative sign is that of A−Bx². This independently explains the single crossing, but tangency and the initial endpoint require the preceding argument; simply counting negative derivative crossings without them is incomplete. The Wronskian route is stronger and closes those gaps. Thus the first failed shortcut was repaired by a materially different integrating-factor/Wronskian mechanism.

## Eligibility decision and strongest objection

**Excluded from discovery credit.** The surviving full ordinary implication is the standard Lagrange identity for two Sturm–Liouville equations plus a single-crossing potential difference and elementary endpoint series. It uses no genuinely new Bessel identity or substantial analytic estimate. The general-order conjecture is resolved by this reduction at the ordinary level, but the strongest substantive/prior-art objection is that this is a routine classical Sturm comparison corollary. The assignment explicitly disallows such credit even if no exact matching printed statement is located. A registry record calling unimodality open is not evidence against this objection. No attempt is made to turn the generic Wronskian lemma, a fixed-order concavity restoration, the already public log-concavity witness, or the ellipse bound into a separate result.

No eligible complete candidate remains, so no nomination or PROOF.md. The mathematical uniform step in the stated unimodality reduction is closed by the case analysis above. What remains unproved is **eligibility/novelty of any substantive new source outcome**, not an all-parameter inequality silently left to finite testing. The sharp all-order/all-scale log-concavity region is not solved here and was not substituted for the actual source question. In particular proving concavity only above order1/2 would be a new restricted problem, not the original universal claim; no such claim is made.

## Falsifiers and exact diagnostics

`sh run.sh` reproduces 2295 exact rational coefficient identities for the Wronskian equation through n16 on 135 order/scale pairs, including negative sums, zero sums, equal orders and equal scales. The normalized series coefficient recurrence is c_(k+1)=a² c_k/[4(k+1)(k+u+1)]. At total index n, the independently convolved Wronskian coefficient is w_n=sum_(k+l=n)c_k d_l(u−v+2k−2l); checked identity (s+2n)w_n=A h_n−B h_(n−1). These checks test algebra and normalization, not universality.

Strongest falsifier of the tempting overclaim “the ratio is always increasing”: u=v, a<b has W'<0 and limit W(0)=0, hence is strictly decreasing on the entire half-line. Strongest falsifier of the source's preprint log-concavity is the public certified three-point witness, independently reproduced using sixty terms and a geometric upper tail. In check.py, lower bounds multiply the larger product and upper bounds the smaller; the resulting strict ratio exceeds1.02. A finite partial sum by itself would not establish this inequality. No novel refutation is claimed.

AS512MiB, process CPU210s, sampled group CPU210s, wall230s, BLAS1, sampled group RSS≤512MiB,40ms monitor: all copied unchanged from r55. Exact checker sampled peak12.2MB, wall0.15s. Sampling does not rule out transients between observations. All network helpers were run under this guard; no limit increases.

## Current registries, chronology, source gaps

Five live heads refreshed at15:43:18UTC; all unchanged from r55. Omega dev3b4135a35caa0ae817cf5eca51d605b098027fd2. Instead of trusting r55's capped21-commit delta, fetched the current immutable root, Blueprint subtree, and **complete named D5 and Problems trees**, respectively23236 and1551 entries, both truncated=false. D5 tree56e3ee94625deab6013ba2dca95c587ba1779496, Problems b0dfc749b68f250535c96dfe57d4db34e43f6387. No whole-dev absence claim. Other four unchanged heads use hash-verified named cached scopes with explicit paths in registry-screen.json. Filename hits guide reading only, not absence proofs.

Read actual closest Problems and generated Result.md bodies, including positive-series definition, exact universal claim and result, Gamma/Pochhammer normalization, tail certificate and the explicit exclusion of unimodality from its scope. Commit path history October25 predates this lane. No settlement of unimodality inferred from the distinct log-concavity result. Full D5 body corpus and whole dev are not audited; no novelty PASS.

Published KVZ May20,2025 body and earlier author manuscript both obtained, and their different final clauses checked. arXiv history page saved; detailed latest-version reconciliation beyond the author/published comparison is not claimed. Salazar2607.05538v1 is actual closest Bessel-Riccati companion read at its scope: its Bernstein classification, individual-Bessel concavity and half-order quotient proposition do not constitute a full general-order scale-ratio proof. Classical Nanthanasub–Novaprateep–Wichailukkana2019 published body obtained/read for individual-Bessel log-concavity, differential equation and parameter restrictions; that is a different assertion. No exhaustive companion corpus claim.

Exact URLs, response UTC, byte hashes, failures and derived text/render hashes are in provenance.json/http.jsonl. d-nb429 was not retried; canonical publisher PDF worked. Springer redirects supplied cookie-related URL parameters automatically but returned valid primary PDF bytes; no challenge bypass. No accounts, browser tabs, messages, uploads, git or shared edits.
