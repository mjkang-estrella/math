# r92 research record — 29 October 2026

## Scope and screening

Solo, no children. Writes are confined to this lane; no git, shared-file mutation, browser, credentials, contact, posting or upload. Governing ancestor/batch instructions, ledger, NEXT, prior context and specified registry baseline were read. r91's Poullot family and source-adaptation leads were not revisited; r89/r90 were consulted only through available notes, with no worker polling. All-date `rg -l` screening preceded source investment; duplicate-initial.txt records the initial source-wide screen, duplicate-all.txt and duplicate-reports.txt the refined exact-family screen. The report inventory includes FINDINGS, discovery, SUMMARY and provenance names across every date, not just this batch. Empty exact-report results do not prove literature novelty.

Screened leads:

* Kurşungöz 2502.17117: duplicate in sol-fresh-source-discovery-r40; rejected before proof work.
* Gao–Ruan–Xie 2507.01332v1 Conjectures 1.4/1.5: every finite matroid, loops removed as defined, has unimodal/log-concave inverse Z coefficients. Actual definitions (2)–(3), Proposition 2.1 proof, Lemma 2.2, Proposition 2.3 proof and uniform proof were consulted. Source Theorem 1.6 proves only sparse paving. Actual 2601.17314 successor Theorem 1.7 proof pp23–24 supplies stressed-hyperplane relaxation, not arbitrary-matroid log-concavity. No purported new paving specialization is pursued. Full arbitrary-matroid mechanism is missing; not selected.
* Sagan–Wilson plactic centralizers: source 2410.20460v1 Conjecture 6.3, with actual Corollary 3.3 and Section 5 proofs. Selected ONLY the full log-concavity assertion (c). Positivity is already proved by Sagan–Zhao 2512.21401v1 Theorem 4.2, whose proof was read. Defant 2605.19979 Theorems 4.3/4.7 with proofs pp12–15 settle other source conjectures and are not fresh targets. Actual public n=10 peak proof excludes (d).

## Exact target and quantifiers

For each integer n>=2 define C(1)={w: P(1w)=P(w1)} and c_n(m)=|C(1) intersect [m]^n|. The unique polynomial expansion is

    c_n(m) = sum_{k=0}^{n-1} a[n,k] binom(m,k).

The target is, for EVERY n>=2 and EVERY 2<=k<=n-2,

    a[n,k]^2 >= a[n,k-1] a[n,k+1].

These are all internal indices of the sequence a[n,1],...,a[n,n-1]. Positivity, already known, would then imply unimodality. No claim about a maximum at ceil(n/2) is included. The original source states its polynomial expansions for m>=n; the counting formula below holds for all positive integer m directly, and polynomial uniqueness identifies that same polynomial. The formal value at m=0 is zero for n>=2: only hook tails can contribute at -1, and their alternating binomial sum is (1-1)^(n-1). Thus finite differences at zero are legitimate, not an unproved domain extension.

## Exact reconstruction and proof attempt

Write tail(lambda)=(lambda_2,lambda_3,...). Source Corollary 3.3 says the first row of P(w) consists entirely of ones. Deleting it and subtracting one from all remaining entries bijects with SSYT of shape tail(lambda) on [m-1]; reinstating the all-one row always respects column strictness. RSK's recording tableau gives

    c_n(m) = sum_{lambda partitions n} f^lambda s_tail(lambda)(1^(m-1)).

Hook length and hook content evaluate both factors exactly. This is a classical reconstruction of the source mechanism, not a nominated theorem. `check.py` obtains a[n,k] by forward differences. `analyze.py` reconstructs both bases, verifies their equality at each interpolation point, and uses exact Sturm root counting. `route.py` additionally checks literal word insertion against the formula for all n=2..6,m=1..4 and reconstructs the entire n=10 row through independent corner/horizontal-strip recurrences.

Sagan–Zhao's actual Theorem 4.2 proof gives the more revealing decomposition. All hook shapes together contribute binomial(n-2,k-1) to a[n,k]. For a nonhook lambda, put N=|tail(lambda)|. Each linear extension pi of the source's labeled Ferrers poset contributes

    binom(m+p,N), p=N-des(pi)-2>=0,

and hence binom(p,N-k) in the binomial(m,k) basis, with multiplicity f^lambda. This proves positivity but does not establish log-concavity after summing shapes. A possible proof would have to exploit the exact hook-length weights and coupled descent distributions; arbitrary positive sums do not suffice.

### Failed stronger routes

1. Real-rootedness: already n=6 gives A_6(x)/x = 1+18x+48x^2+41x^3+x^4. The exact Sturm chain in route-results.json has only two negative real roots. Positive coefficients exclude nonnegative roots, so the other two roots are nonreal. Newton's real-rootedness route cannot prove the full source family. This is not a source counterexample.
2. Source-component synchronization: at n=5 the grouped hook vector is u=(0,1,3,3,1); the actual nonhook shape (3,2), before its positive f-weight, contributes v=(0,0,1,0,0). At k=3 the mixed coefficient 2u_k v_k-u_(k-1)v_(k+1)-v_(k-1)u_(k+1) equals -1. Thus even these actual component types fail the pairwise nonnegative-mixed-term criterion. Their specific source-weighted full sum still passes; this does not refute the conjecture.
3. Changing bases: if c_n(m)=sum b[n,j] binom(m-1,j-1), then b[n,j]=a[n,j-1]+a[n,j], with a[n,0]=a[n,n]=0. Sagan–Zhao Conjecture 4.6 is log-concavity of b, not of a. `shift.py` gives positive-endpoint synthetic rows for which b is log-concave but a is not. Therefore proving that separate conjecture alone cannot finish this target. These synthetic rows are not centralizer rows.

The stronger diagnostic a[n,k]/binom(n-2,k-1) is log-concave in all 561 tested inequalities n<=36. No Lorentzian representation, closed recurrence preserving this normalization, injection, or signed-term cancellation is proved. Repeating larger tables would not close the gap.

## Public duplicate and chronology

Locally the mode at n=10 occurs at k=6, with a_5=75095<a_6=88704. Before any nomination, live search found fengqiaoqu/plactic-peak-counterexample. We fetched its HEAD and then pinned actual README, proof.zh-CN.md, summary.en.md and computation scripts at da399730a04f1044f72a413cee21a9319021cac1, committed 2026-10-22T05:22:36Z. Its proof supplies precisely the same RSK/hook-content mechanism and exact vector (0,1,250,4917,29648,75095,88704,43414,4861,1). Its independent branching/tableau checks are also described. This predates this lane by a week and is a substantive exact public duplicate, irrespective of its lack of external peer review. It resolves only mode-location (d); neither that proof nor source Theorem 4.2 proves (c).

Original plactic source v1: 2024-10-27. Sagan–Zhao successor v1: 2025-12-24; publisher page dated 2026-06-24. Inverse Z source v1: 2025-07-02. Original source author-hosted published PDF returned a 212-byte Incapsula challenge, not a PDF. That host was not retried or bypassed. arXiv was a separately discovered primary preprint, not evidence that the unread journal body matches word for word. Published 7.3 numbering is supported by public excerpts/peak attribution, with direct journal-body equivalence remaining HOLD.

## Current registries and access limits

Baseline root-edge-irregulator-final-freeze-r1 contains complete tree inventories Omega1b999d9fda71df7537b62327147496d64a6f66ef and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. r88/r86/r91 record intervening deltas; r91 latest Omega549177fd878744e25dce688cbf94dc2955e8958f is the comparison base here. Fresh public API reads at 2026-10-29T19:03 UTC give Omega2130bf544f7858fc3c142bb9623b7ba9464e22ba and unchanged OpenAI. The Omega comparison returns 13 commits and 5 changed files. Actual returned patches were scanned, not just names; no selected-family hit appears. Baseline complete inventories have no exact plactic-centralizer or inverse-Z path hit. This does NOT establish a semantic all-proof audit, and the inherited intermediate inventories were not re-audited in full. Broadly titled unexamined bodies remain a coverage gap. Public peak proof is the decisive exclusion for (d), independent of registry filenames or solution badges.

No 403/429 retry loop, alternate proxy, challenge execution, account or browser was used. Search coverage is bounded and not systematic worldwide prior art. Some fetched HTML URLs carry a cookie error parameter; stored bodies are retained, and no access gap is silently cleared. Source records, retrieved dates and byte hashes are in http.json and provenance.json.

## Falsifiers, objections and exact remaining gap

A single literal centralizer row with a[n,k]^2<a[n,k-1]a[n,k+1] would refute the chosen universal target. A direct disagreement between insertion enumeration and reconstruction would invalidate the checker. A complete earlier proof of (c), or a theorem whose actual proof supplies the weighted coupled-descent inequality, would exclude this target. The known n=10 mode defect, nonreal roots and negative mixed terms are none of these falsifiers.

Remaining gap: prove the displayed log-concavity inequality uniformly for the exact weighted Ferrers-descent sum, or exhibit a genuine negative coefficient determinant for that sum. All currently verified statements are classical reductions, finite diagnostics or proof-route obstructions. No full result, eligibility PASS, or priority clearance is claimed.
