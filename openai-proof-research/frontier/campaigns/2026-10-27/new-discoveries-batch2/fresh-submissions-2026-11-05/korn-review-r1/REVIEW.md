# Independent adversarial review: MathDB 329722

Review date: 2026-11-05 local / 2026-11-06 UTC. Disposition: **ordinary mathematics passes; literal 2015 conjecture is refuted; novelty remains unestablished; do not award substantive discovery credit or begin Lean on this handback.** No author acceptance is adopted.

Read ancestor AGENTS, upstream provenance/catalogue, campaign ledger/context, sibling `analysis/329722-proof.md`, `REPORT.md`, `results.json`, the diagnostic source and primary source bodies. Writes are confined to this directory. No children, implementation, commits, messages or posting.

## Separate verdicts

| Gate | Verdict |
|---|---|
| Correctness | PASS, for the explicit universal boundary inequality on the fixed disk, with Euclidean vector and Frobenius matrix norms. |
| Literal fidelity | PASS for arXiv:1501.05340v1 Conjecture 2.2/(2.5), with a material PDE-intent qualification. Not a demonstrated resolution of the 2006 original conjecture. |
| Novelty | HOLD. No exact public predecessor located in the bounded search. Missing primary bodies and incomplete current-registry coverage preclude clearance. No global priority claim. |
| Mathematical significance | DO NOT ACCEPT under this campaign's substantive-credit standard. The demonstrated endpoint is an elementary boundary-jet obstruction to an overbroad displayed assertion. There is no demonstrated resolution of the original restricted PDE target, or additional nonroutine mathematical ingredient. |
| Formalization | DEFER. There is a valid analytic endpoint, but significance and source-scope holds do not warrant the substantial trace/integration formalization work now. |

## Independent mathematics

Write w=bar(z), s=zw. The candidate complex polynomial is

    U = [3 z^(k+1) - z^(k+2)w + (2k+3)zw^k - (2k+1)z²w^(k+1)]/4.

For every integer k>=1 this really is polynomial, including k=1. I independently differentiated before substituting w=1/z:

    U_z = [3(k+1)z^k -(k+2)z^(k+1)w +(2k+3)w^k -2(2k+1)zw^(k+1)]/4,
    U_w = [-z^(k+2) +k(2k+3)zw^(k-1) -(k+1)(2k+1)z²w^k]/4.

On z=exp(iθ), these simplify to

    U = exp(iθ)cos(kθ),
    U_z = cos(kθ)/2 + i k sin(kθ),
    U_w = -exp(2iθ)cos(kθ)/2.

These are derivatives of the actual field: the real Frechet derivative is the real-linear map

    dU_z(h) = U_z h + U_w conjugate(h).

Thus no arbitrary boundary matrix has been substituted for a Jacobian. In Cartesian entries, U_z=((u1,x+u2,y)+i(u2,x-u1,y))/2 and U_w=((u1,x-u2,y)+i(u2,x+u1,y))/2. Consequently

    |Du|_F² = 2(|U_z|²+|U_w|²),
    |sym Du|_F² = 2(Re U_z)²+2|U_w|².

They give |Du|²=2k²sin²(kθ)+cos²(kθ), |sym Du|²=cos²(kθ), |u|²=cos²(kθ). This independently verifies the polar calculation.

The radial coefficients in the proposal also agree: a=(k+3)r^(k+1)/2-(k+1)r^(k+3)/2 and b=k(r^(k+3)-r^(k+1))/2 give a(1)=1, a'(1)=0, b(1)=0, b'(1)=k. The moving-frame Jacobian is Q^T(Du)Q, with columns differentiated in unit radial/tangential directions. Its boundary entries are exactly [[0,-k sin(kθ)],[k sin(kθ),cos(kθ)]]. Using Q on both sides preserves symmetric parts and Frobenius norms. A transposed gradient convention does not change the three norms.

The source defines strain with the factor 1/2 and transpose, not conjugate transpose. Its standard L² matrix product is consistent with Frobenius contraction; the real subclass avoids any complex-convention issue. Even an equivalent finite-dimensional matrix norm could not rescue a uniform estimate, though the exact π identities use Frobenius.

Every derivative through order two of a polynomial is bounded on the closed disk and is square integrable on its finite area. Classical derivatives are its weak derivatives, so restriction belongs to H²(D;R²), and hence also to the source's complex vector space. There is no uniform H² bound in k, and none is required. Polynomial values at the origin cause no singularity.

For the smooth disk, the H² trace of u and the H¹ traces of its first derivatives coincide with classical boundary restriction. The derivative traces lie in H^(1/2)(∂D), in particular L²; u has the stronger H^(3/2) trace. Applying the linear symmetric-part operation commutes with these traces. Thus the integrals are the advertised Sobolev boundary norms, not merely unrelated parametrized quantities.

The parametrization γ(θ)=(cosθ,sinθ) has speed one, covers the circle once on [0,2π), and its duplicate endpoint has zero arclength measure. Therefore ∫∂D F ds=∫0^(2π) F(γ(θ))dθ. Elementary double-angle integration gives π for each squared sine and cosine at every positive integer k. The exact norm squares, in order displacement/strain/gradient, are π, π, π(2k²+1). Given any proposed finite K>0, an integer k>K+1 violates the inequality. A single smooth bounded strictly star-shaped domain suffices; no variation of domain or frequency is hidden. On the disk x·n=1 and diameter=2.

I read the exact-rational diagnostic, including the Wirtinger norm and real-part Fourier formulas, and reran its 64 cases with `__file__` redirected into this directory so the sibling was not modified. See `korn-exact-diagnostic.json`. The independent all-k derivation above, rather than this finite rerun, is the proof.

## Source scope: actual assertions versus PDE intent

Primary receipt: current arXiv PDF fetched directly, SHA256 b8cc3b7a36f8f3ef71890c90952b8b79b747be28532824eafd397af161f63ca2, identical to the sibling's v1. Current arXiv history lists only v1. Printed p2 defines d=2,3 and the elasticity/impedance problem; p3 imposes strict star-shapedness and standard complex L² conventions; printed p4 gives the universal H² quantifier in Conjecture 2.2 and equation (2.5). Nothing in that displayed assertion imposes a differential equation or homogeneous boundary condition. Its preceding prose does say the estimate is needed for the solution of (2.1). Theorem 2.3 then deliberately assumes membership in V_K, the class satisfying the inequality. Printed pp9–10, Theorem 4.1/Remark 4.2 distinguish the conditional improved estimate. Refuting the universal conjecture does not refute a theorem conditional on V_K.

A materially important lawful primary comparison is now available: **Cummings 2001 dissertation**, downloaded from Tennessee's public repository, printed pp24 and 39–40 (PDF p50 for Conjecture 1). Its (2.5) uses homogeneous impedance boundary data. Conjecture 1 is explicitly conditioned on solving (2.5), and introduces alternative inequalities. The scanned equation extraction is poor; I do not certify its exact formulas from the OCR, or identify them with 2015 (2.5). The solution restriction itself is unambiguous in the body. This thesis is evidence about the precursor's intent, not a substitute for reading the 2006 article.

**Lorton 2014 dissertation**, also obtained from Tennessee's public repository, printed pp21–22 (PDF p36) repeats the universal H² version as Conjecture 2.3.4/(2.24). The preceding paragraph discusses Helmholtz solutions, and the future-directions section, printed p197, describes the target expressly as a boundary inequality for solutions of the elastic Helmholtz equations. This supplies primary-body evidence that the universal wording and the intended application differ. It does not erase the universal displayed claim.

One must specify what “solutions” means. At fixed positive parameters, every candidate polynomial solves (1.1)–(1.2) for manufactured smooth f=-ω²ρu-div σ(u) and g=iωAu+σ(u)n. Thus merely adding “PDE solutions” with arbitrary f,g and a data-independent K does not exclude these fields. By contrast, these particular real fields fail homogeneous impedance data: on ∂D, div u=cos(kθ), ε(u)n=0, so σ(u)n=λcos(kθ)n; the imaginary part of iωAu is nonzero wherever u is nonzero for SPD A. They also cannot solve the homogeneous positive-frequency bulk equation: its highest polynomial degree cannot cancel against the degree-lowering elastic operator. Claims about either homogeneous restriction require a different argument. No such restriction is silently granted or refuted here.

The published 2016 Feng–Lorton version is DOI 10.1007/s10915-016-0219-4, published 14 May 2016, revised 16 February 2016. The publisher provides subscription preview only. Its full body has not been checked; the arXiv file alone does not establish that the published statement retained universal scope.

## Significance objection with an actual construction

The obstruction is boundary-jet freedom, not a delicate feature of the proposed polynomial. Choose a smooth radial cutoff χ equal to one near r=1 and zero near r=0. For any smooth periodic real f, set

    v(r,θ)=χ(r)[f(θ)e_r -(r-1)f'(θ)e_θ].

This is smooth on the closed disk because it vanishes on a neighborhood of the polar singularity. On r=1 its actual derivative in the radial/tangential frame is

    [[0,f'(θ)],[-f'(θ),f(θ)]],    sym Dv=diag(0,f(θ)).

Thus the proposed universal inequality would force

    2||f'||² + ||f||² <= 2K||f||²

for every smooth periodic f. Taking f=cos(kθ) is the immediate contradiction. This does not invoke a general trace-extension theorem: the extension is explicit. The candidate is a polynomial realization of exactly these boundary jets, removing the cutoff at no change to the obstruction.

This is a useful exact-source correction and a valid infinite sequence on a fixed admissible domain. It is more than a bad numeric example. Nevertheless the source's named PDE difficulty, the elementary jet mechanism, and the distinction already visible in the 2001/2014 bodies make substantive discovery credit unwarranted on present evidence. I have not proved that an earlier author published this exact correction; routine mechanism and known published resolution are separate grounds. Neither a short proof nor an open database record settles significance. The author's claim that this is not an endpoint defect does not answer this objection.

## Prior art, registries and duplicates: bounded findings

Geng–Shen–Song arXiv:1608.07736v1 was read in the sibling's actual full text, especially introduction (1.14)–(1.17), Section 5 Theorem 5.1 and Lemma 5.2. Its boundary Korn estimate (1.16)/(5.2) assumes homogeneous elasticity solutions, nontangential boundary control and coefficient/domain hypotheses, and includes an interior gradient term scaled by diameter^(-1/2). The harmonic lemma is also restricted to harmonic fields. These are not the universal H² inequality. They neither contradict the candidate nor certify originality. The older harmonic-boundary literature it cites was not fully audited.

Lawful attempts for Cummings–Feng 2006 DOI 10.1142/S021820250600108X: publisher PDF again returns 403 (receipt retained); exact-title/DOI searches and author/institutional routes did not yield a verified lawful public article body. Search surfaced a third-party Scribd transcription, which suggests a solution-restricted conjecture with a different right-hand side. It was not used as cleared primary evidence, downloaded through a restricted endpoint, or treated as proof of the exact 2006 statement. The lawful 2001 thesis is separately cited above. The 2006 source hold remains OPEN. No inference from an abstract closes it.

Live checks at the receipt times: openai/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae. Its freshly retrieved complete preprints subtree has 13,578 entries, truncated=false. Broad path terms Korn/Cummings/Lorton/elastic/Sobolev/trace/Helmholtz/boundary/strain/Feng selected 371 textual bodies, all fetched successfully at that immutable head; substantive body searches found no Korn/Cummings/Lorton/source-ID hit. The selection and each URL/hash are in `math-preprints-body-index.json` and `source-receipts.json`. This is a broad relevant-body screen, not a semantic reading of every preprint.

The omega registry **advanced during review**: current dev head bff0276bdd99004a6c0549292f9c57301085af12, versus sibling head 5a97247bf6ad10485d8891db5430b9e34def4933. Fetch of the current root tree returned an explicit GitHub API rate-limit 403; I did not retry around that limit. I used the existing complete Library subtree (2,762 entries, truncated=false) at the earlier head, and fetched/search-read all 17 broadly relevant textual paths at that pinned head; none contained target terms. Their URLs/hashes are in `extra-source-receipts.json`. A further 177 already-downloaded registry bodies in the sibling metric lane were searched in place, with no target-term hits (`reused-registry-body-search.json`). This does NOT close the new-head delta, the current Problems subtree, all Lean sources, or global semantic coverage. Current-registry clearance remains held.

Live MathDB response matches the sibling hash and remains open with no solutions. This is status evidence only. Bounded web searches for boundary Korn/refutation/Feng/Lorton, including EulerSolve and Crab site queries, found no exact public resolution; irrelevant search hits confer no clearance. No exhaustive citation database search was performed.

Read-only git all-ref message search for target/topic names produced no matching commit message; the full all-ref content-diff search was bounded at 55 seconds and timed out. The completed all-ref object/path screen inspected 466,827 object/path lines and found 12 topic/name hits (`all-ref-path-screen.json`). The old `sol-fresh-source-discovery-r201/korn-early-screen.json` is a fractional-Korn screen (pattern includes arXiv:2302.14588), not this boundary problem; its source titles were checked. Other hits include unrelated Korn literature and accidental path text. This is not a substitute for semantic history coverage. Working campaign body searches found the sibling proposal/status/raw database inventory, not an earlier substantive Korn result. Numeric ID-only matches in unrelated certificates were excluded as noise. The campaign ledgers/context contain no identified accepted same-family outcome. No duplicate acceptance is demonstrated, and absence of duplicates is not certified across all history.

## Concrete handback and formal endpoint

Required corrections before any broader claim: name the result as failure of the **displayed universal** Feng–Lorton estimate; do not call it resolution of the original 2006 PDE conjecture; cite the 2001/2014 scope evidence; retain the published-version, original-body, current-registry and history limitations. No global priority statement.

If a future scope/significance decision nevertheless warrants formalization, the endpoint must negate a uniform boundary inequality for restrictions of these actual real polynomials to the disk. It must prove their Frechet derivatives, H² membership and compatibility of weak/classical derivatives, the Sobolev-trace restrictions, Frobenius contraction/symmetric-part identities, and equivalence of circle-parametrized integrals to arclength L² norms. Boundary matrices with three stipulated integrals, or a finite k sweep, do not discharge this endpoint. These bridges are mathematically valid here, but no Lean library implementation or availability audit was performed. Under current evidence, defer that investment and award zero discovery credit.
