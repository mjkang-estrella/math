# r182: one fresh exact question; full resolution remains open

Read the ancestor and batch AGENTS.md and archived NEXT/ledger/prior context. Counts as read: 9 additional /39 total, next40. Nothing is credited or edited in shared state. Solo research only.

## Early qualification and bounded reconnaissance

Before mathematical work, work.py init merged r179/r178/r177/r176/r170 history indexes and refreshed actual bytes: 2,515 records, nine changed/new, zero missing; ten r111–113 entries retained. No new echo exclusions were made. Inherited counterpart/provenance qualification files are copied; no date/lane blanket exclusions. Sixteen relevant originals, including r111–113, are copied byte-for-byte with original-copy-provenance.json. early-screen.json, focused-screen.json and exact-author-screen.json record the identifier/title/author/alias screens. Some author matches are unrelated people; these are not duplicate findings.

Broad public search covered irreducibility, divisibility, finite-field permutations, binomial positivity and Hankel determinants, then narrowed to exact sources. Early rejections are reconnaissance, not three fresh statements investigated:

* Gatzweiler–Krattenthaler arXiv2502.06032: r23 exact prior selection; retire, no mathematical reopening.
* Sun arXiv2505.02767, rising-binomial q-log-convexity: r38/r67 and an explicit current public resolution body identify overlap. Retire; fetched Sun bytes are unused reconnaissance, not a new theorem dependency.
* Luo–She arXiv2610.06289 / Sun circular permutations: r41 exact prior public-refutation disposition. Retire without reopening.
* Permutation-trinomial/pentanomial papers whose search descriptions already announce solutions: no original unresolved statement selected from these.
* Wang–Zhang Motzkin determinants: search surfaced companion2503.17187. Not selected, not claimed publicly resolved from its abstract, and no exact conjecture comparison or mathematical investment undertaken.

This is not a three-old-lead stopping rule: continued screening reached the genuinely different Fernando–Kousik question below. At most one fresh exact unresolved question is selected. Same-source Conjecture5.23 is an eligibility screen with a complete routine bridge, below.

## Primary statement and chronology

Neranga Fernando and Bhitali Kousik, **A further study of polynomial g_{n,q} over finite fields**, DOI10.48550/arXiv.2606.01037. Latest actual arXiv landing page lists only v1, submitted 31May2026 06:04:17 UTC; actual PDF is21pages. No journal reference was observed on that landing page; no independently authenticated published version is claimed. Retrieved current landing page and PDF at actual UTC2026-10-30T04:01:30+00:00. Exact bytes, SHA256 and access receipts: http.jsonl, sources/finite*.

The definition on pp1–2 is the unique polynomial g_{n,q} satisfying sum_{a in F_q}(X+a)^n=g_{n,q}(X^q-X). On p3, S_k(X)=sum_{i=0}^{k-1}X^{q^i}. **Question6.2, p17**, fixes q=4 and every integer e>2, puts n=1+4^{e-2}+4^{e-1}+2*4^e, and asks for conditions on e under which g_{n,4} permutes F_{4^e}. Its displayed polynomial is

g = S_{e-1} S_e + S_2^{4^{e-2}} S_{e-1} + S_e^2.

The desired full endpoint is an explicit necessary-and-sufficient classification for **every integer e>2**, not the source's e=3 example or another finite extension. Working hypothesis suggested by controls: only e=3. This hypothesis is NOT proved.

## Material companion proof bodies read early

Fernando–Hou–Lappano, arXiv1208.2942v1 (14Aug2012), published FFA22(2013)122–158, DOI10.1016/j.ffa.2013.01.001: read Theorems6.10–6.12 and their proofs, character-sum Lemma6.13 and Appendix table. The actual table leaves (149,3;4) without explanation. Theorem6.12 concerns n=1+4^e+2*4^a+4^b and g=S_a^2+S_b S_e, under explicit gcd/parity hypotheses. That expression preserves a trace quotient, enabling the displayed linearized difference proof. No identity identifying the present all-e source family with this class was established.

Fernando–Hou, arXiv1503.03162v1 (11Mar2015), published FFA37(2016)14–27: read Theorem1.1, Theorem2.1 proof and Proposition3.1 proof, plus applications3.3–3.7 and table. Its criterion requires a permutation on the trace quotient, affine linearized restrictions to every trace fiber, and a uniform associate-determinant gcd. Our map's trace is Tr(x^5), not a function of Tr(x) supplied by those results. Thus the criterion is not already a closed proof here. Journal bodies were not fetched from the denied publisher; no arXiv/VoR identity certification.

## Strongest sustained route

Let K=F_{4^e}, T=Tr_{K/F4}, y=x^{4^{e-2}}, z=x^{4^{e-1}}=y^4, t=T(x)=T(y). Then S_{e-1}=t+z and S_2^{4^{e-2}}=y+z. Direct multiplication in characteristic2 gives

g(x)=t(t+z)+(y+z)(t+z)+t^2 = y^8+y^5+yT(y).

Frobenius is bijective, so the literal source classification is exactly the classification of F(y)=y^8+y^5+yT(y). Every e even fails since F(0)=F(1)=0. This trivial necessary condition receives no outcome credit. Also T(F(y))=T(y^5): T(y^8)=T(y)^2 and T(yT(y))=T(y)^2 cancel. This explains the missing trace-quotient step in the companion adaptation.

For arbitrary a≠0, define

C_a=a^8+a^5+aT(a),
L_a(x)=a x^4+a^4 x+xT(a)+aT(x).

Then F(x+a)+F(x)=C_a+L_a(x). This is an exact universal identity, and L_a is F2-linear (indeed F4-linear). F permutes K iff C_a is outside im(L_a) for every nonzero a. This equivalence is a reduction, not a solved classification; evaluating all its ranks still depends on e and a.

Writing s=T(a), t=T(x) reduces the collision problem to the sixteen trace cases

a x^4+(a^4+s)x+a t+a^8+a^5+a s=0,
T(a)=s, T(x)=t, a≠0, s,t∈F4.

For s=t=0 and x=az this simplifies to the fixed curve z^4+z=a^3+1, with T(a)=T(az)=0. The trace constraints can themselves be represented by b^4+b=a and c^4+c=az. Thus a point over F_{4^e} on this fixed affine cover with a≠0 yields a collision for the literal source polynomial. This is a concrete universal strategy: establish an absolutely irreducible F4 component, normalize it, bound its genus and deleted/bad points, apply a uniform finite-field point bound, and classify the finitely many remaining e by exact arguments. Alternatively solve all sixteen linearized trace systems directly. Neither plan has been completed.

Important negative control: the s=t=0 curve has zero admissible (a,z) pairs at e=5 although F is not a permutation there. Therefore that restricted curve cannot alone classify all degrees without separately treating the residual degrees/other traces. No genus, irreducibility or effective threshold is asserted. These are substantive missing proofs, not administrative cleanup.

## Exact bounded controls and strongest objections

checks.py builds F2[X]/f with irreducibility verified by Frobenius/gcd, over e=3..7. All21,824 source evaluations agree with the normal form after Frobenius;109,120 derivative controls pass. Image sizes are64,157,619,2506,10147, respectively, out of64,256,1024,4096,16384. Curve pair counts are0,12,0,360,1344. Exact field moduli and witnesses are in checks.json. No floating-point arithmetic, Lean or manuscript. These controls do NOT establish any all-e statement or a new full source resolution.

Strongest objections: (1) no universal odd-e collision existence, so even the proposed classification remains unproved; (2) the curve may split into components over an extension or have trace-cover dependencies, invalidating a naive Weil argument; (3) companion conventional-associate machinery applies only after missing quotient/affine-fiber hypotheses; (4) current registry HEAD/body clearance is unavailable, so new-to-literature status is HOLD; (5) source is a classification question, and a tautological matrix-rank test alone is not a substantive answer; (6) any eventual finite-threshold proof must include an explicit justified threshold and every residual degree, not a finite table promoted to a theorem.

## Same-source classical exclusion: Conjecture5.23

This is not nominated. For all finite fields F_Q, k≥1, ell≥1 and univariate g=g_{n,q}, it asserts that g(sum_i X_i^ell) has constant fibers Q^{k-1} iff gcd(ell,Q-1)=1 and g permutes F_Q. Actual statement pp16–17 and surrounding proofs pp13–16 read.

Complete classical bridge: let A=(F_Q,+), and let mu(b)=#{x:x^ell=b}. The fiber-count function for sum_i x_i^ell is the k-fold additive convolution mu^{*k}. If the composition with g has constant nonzero fibers, it is surjective. Consequently g is surjective on A, hence bijective. Its fibers merely relabel the fibers of the sum, so mu^{*k} is constant Q^{k-1}. For each nontrivial additive character chi, finite-sum multiplicativity gives hat(mu^{*k})(chi)=hat(mu)(chi)^k=0, hence hat(mu)(chi)=0 over C. Finite character orthogonality then gives mu(b)=Q^{-1}sum_chi hat(mu)(chi)chi(-b)=1 for every b, since hat(mu)(1)=Q. Thus x↦x^ell is bijective, equivalently gcd(ell,Q-1)=1 by cyclicity of F_Q^*. Conversely, if that gcd is1, fixing the first k-1 variables leaves exactly one last variable for each sum value. A bijective g preserves that count. This covers k=1, all characteristics, all n for which g is defined, and all ell≥1. No positivity or even-characteristic assumption is needed. Character orthogonality follows from sum_x chi(x)=chi(a)sum_x chi(x) with chi(a)≠1, plus the full dual having Q characters.

This is a routine classical convolution/character argument, not a substantive discovery. No claim of a matching earlier exact public source resolution is made without its body. The bridge is self-contained; the attempted Conrad URL returned404 and was not a dependency. Do not credit it just because the source proof stops after special diagonal-equation cases.

## Prior-art and access limits

Current public exact-title/identifier/author/normal-form searches were conducted; final exact queries and returned results archived in search-receipt.json. No matching full resolution body was found in that bounded search, which is not exhaustive novelty clearance. Actual cached registry trees were screened across11 inputs (564,450 entries including overlaps), receipts and broad hits in registry-screen.json. Names are reconnaissance only: unrelated trace/diagonal hits were not upgraded to proof matches. The first13-path wrapper-only screen was recognized as inadequate and replaced by actual input-tree screening, without any novelty conclusion based on it.

No current registry HEAD is authenticated here. Existing capped-history/missing-merge obligations remain PARKED; no reconstruction or fresh-HEAD loop. No GitHub API/raw/codeload/patch/diff, ScienceDirect, Google challenge, denied IEEE/OpenReview/d-nb endpoint retried. http.jsonl records a single404 for an untried classical note; no403/429/challenge occurred in this lane. No browser, external messages/posts/uploads, git, Lean, manuscript, ledger or count edits. Research freshness is qualified by these explicit limits; root owns further review/investment/acceptance.
