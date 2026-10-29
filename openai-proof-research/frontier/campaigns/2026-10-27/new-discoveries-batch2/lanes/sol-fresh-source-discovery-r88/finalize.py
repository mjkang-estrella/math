import pathlib,json,datetime,hashlib,re
L=pathlib.Path(__file__).resolve().parent;B=L.parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
# Read patches as well as path names; no claim of semantic worldwide clearance.
d=json.loads((L/'sources/omega-corrected-delta.json').read_text())
patchhits=[{'filename':f['filename'],'patch':f.get('patch','')} for f in d.get('files',[]) if re.search(r'Fuss.Narayana|335387|1702\.07822|Wang.{0,20}Yang',f.get('patch',''),re.I)]
(L/'delta-content-hits.json').write_text(json.dumps({'hits':patchhits,'files_without_patch':sum('patch' not in f for f in d.get('files',[])),'limit':'GitHub patches can be truncated or omitted; absence is not semantic clearance.'},indent=2))
(L/'SUMMARY.md').write_text('''# r88 — zero credit, no nomination

Wang–Yang, *Total positivity of Narayana matrices*, Conjecture 4.1 (author-hosted manuscript dated 7 November 2017, pp8–9) remains unresolved in this lane. The full target is all four Fuss–Narayana triangles TP and both squares STP for every integer m>=2 and arbitrary finite minors. No parameter fragment is nominated.

Three source leads screened. The Toeplitz–Hankel conjecture is proved in its own paper. The spectral-spread lead was not invested in: a public proof claim and a blocked primary body prevent qualification. Fuss–Narayana was pursued using the actual source proofs and exact polynomial collocation; its all-minor gap remains. No Lean, paper, PROOF.md, acceptance, or count change. Counts remain 8 additional / 38 total.

123,480 small literal minors and 800 sparse square minors pass, as do 2,184 exact identities. These are diagnostics, not a proof; the small checks are weaker than the source's reported first-ten-row checks. The naive nonnegative-production-matrix route fails, with exact negative entries at m=2. Closest successor-body and semantic current-prior comparison remain HOLD because of access/coverage limits. See discovery.md, http.json, registry-audit.json and check-results.json.
''')
(L/'discovery.md').write_text(r'''# Source discovery and attempted full resolution

Disposition: UNRESOLVED_ZERO_NO_NOMINATION. Only this assigned lane was written. No children, git operations, browser, account actions, contacts, posting, uploads, shared edits, Lean or manuscript.

## Early eligibility and source screens

Read ancestor and batch AGENTS, NEXT, ledger and prior-campaign-context; full JSON loaded and substantive arrays retained in context.json. Initial all-date `rg -l` filename-first screen included FINDINGS/discovery/SUMMARY/provenance before downloads. Later exact screen included REPORT/COMPARISON. duplicate-initial.txt has an incidental root-jacobi provenance hit under broad Narayana vocabulary; exact Fuss-Narayana/335387/1702.07822 report screen is empty. This is a bounded text finding, not a novelty claim. Broad search also hit an unrelated Boltzmann COMPARISON body, which was read and discarded. Available r86 progress (analysis/routine shape result) and r87 context/target inventory were read; no claim to know unpublished progress. All named r80–r85 and campaign exclusions were honored, including the entire Miller–Reiner family, connected W2 and Stanley Schubert determinants.

1. Amdeberhan–Koutschan–Zeilberger, *A tale of Toeplitz plus Hankel determinants*, author PDF https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/tem2.pdf. Conjecture1 gives a product for det T_{n,m}(x), T_ij=binom(x+m,j-i+m)-binom(x+m,m-i-j-1). Read the actual Theorem2.1 condensation proof, Corollary2.2 substitution and Theorem3.1 constant-term proof through its final common integrand. The latter identifies det T with det B and explicitly proves Conjecture1. Rejected before new proof investment. The final q-analogue question is not a precisely specified formula and is not selected.
2. You–Ren–Yu, *Distance and distance signless Laplacian spread of connected graphs*, arXiv1607.00473 / DAM223(2017)140–147. Navigation https://mathdb.com/p/333521/minimum-distance-signless-laplacian-spread-among-bipartite-g reports an August26,2026 submitted proof. That report is not accepted as a verified theorem. Author-hosted VoR URL https://statics.scnu.edu.cn/pics/userfiles/2024/1211/20241211090841220.pdf returned HTTP200 but a 438-byte blocking HTML page, not PDF. Saved verbatim under spread.pdf, failed pdftotext explicitly logged. No challenge retry, alternate bypass, or spectral computation. Exact published quantifiers/proof comparison unavailable; screen HOLD, no discovery investment.
3. Selected: Yi Wang and Arthur L.B. Yang, *Total positivity of Narayana matrices*, https://cfc.nankai.edu.cn/_upload/article/files/ca/07/264e89bc4d9bb418a6d91d482b90/ef62459f-bec2-470d-8199-b57a790de20a.pdf, author manuscript footer 7 November2017, Conjecture4.1 pp8–9. Canonical identifier arXiv1702.07822. This is a concrete all-minors matrix statement rather than a famous broad conjecture or easy fixed-parameter instance. The initially credible route was explicit factorial normalization plus PF/moment or polynomial-collocation factorization.

## Literal target and closest primary proof bodies

For every integer m>=2 and n>=k>=0, set
A_m(n,k)=binom(n+1,k)binom(m(n+1),n-k)/(n+1),
B_m(n,k)=binom(n,k)binom(mn,n-k).
Extend triangle entries by zero for k>n. All four matrices A_m(n,k), A_m(n,n-k), B_m(n,k), B_m(n,n-k), n,k>=0, must have every finite minor nonnegative. Both squares A_m(n+k,k), B_m(n+k,k) must have every finite minor strictly positive: arbitrary order r>=1 and arbitrary strictly increasing nonnegative row and column indices. The source says m>=2; MathDB navigation restates m>=1, but the source m=1 case is already paid.

Read source Proposition2.1, Lemma2.2, Theorem2.3 and proofs, Lemmas3.1/3.2 and Theorem3.3 with proofs. The ordinary/generalized-tail Narayana triangles normalize to a Toeplitz reciprocal-factorial PF sequence. Ordinary squares normalize to a Hankel product of shifted factorial moments. Source parameter m in N_A,<m> (2.1) is a DIFFERENT tail parameter, not the Fuss parameter in Conjecture4.1. Hence those printed proofs do not immediately resolve this target. The source itself reports first-ten-row/column checks for Fuss m2..10.

Closest successor leads: Petreolle–Sokal–Zhu arXiv1807.03271, coefficientwise Hankel positivity of multivariate Fuss–Narayana polynomial sequences; Bao-Xuan Zhu JLMS113(2026)e70450, DOI10.1112/jlms.70450, Riordan-array and Fuss–Narayana–Riordan positivity. Their titles/abstracts and indexed theorem snippets are navigation ONLY. The requested UCL full PDF and Wiley full body each returned403; no retries or bypass. No theorem/proof-body admission or non-subsumption claim for these two. A row-generating-polynomial Hankel theorem is not silently identified with coefficient-matrix TP or the reindexed square; an explicit bridge is required. This unresolved actual-body comparison prevents eligibility clearance.

## Sustained full-scope algebraic attempt

Define, for every integer n>=0, m>=2, c in {0,1},
q_{m,n,c}(x)= product_{j=1}^n(x+j) product_{j=0}^{n-1}(m(x+n+c)-j).
Empty products are1. Direct factorial cancellation, without approximation, gives for all k>=0:
B_m(n+k,k)=q_{m,n,0}(k)/(n!)^2,
A_m(n+k,k)=q_{m,n,1}(k)/(n!(n+1)!).
For B, cancel (n+k)!/k! to (k+1)...(k+n), and (m(n+k))!/(m(n+k)-n)! to the second falling-factorial product. For A, the prefactor binom(n+k+1,k)/(n+k+1) cancels to (n+k)!/[k!(n+1)!], and the second binomial contributes falling(m(n+k+1),n)/n!. Thus both square claims reduce exactly to strict positivity of det[q_{m,n_i,c}(k_j)] for arbitrary row indices n_i and column indices k_j. This retains the full parameter and index ranges; it does NOT prove positivity.

A possible Cauchy–Binet route writes q_n(x)=sum_d C(n,d)x^d. If the infinite coefficient array C is TP with enough strictly positive minors, multiplication by the monomial evaluation kernel would give the desired collocation positivity (with care at x=0 and the strict witness). All q_n have nonnegative coefficients and only nonpositive real roots. Neither fact alone proves the needed TP coefficient array. No all-order factorization, compatible planar network, or nonintersecting path bijection was found. The four triangular claims remain separately unproved.

The direct production-matrix route fails even before a TP test. Let T=[B_2(n,k)] and S=[B_2(n+1,k)], and solve T P=S by triangular elimination (diagonal T=1). Its first rows are
P_0=(2,1,0,...), P_1=(2,6,1,0,...), P_2=(-8,-9,10,1,0,...).
Indeed B2 rows0..3 are (1), (2,1), (6,8,1), (20,45,18,1). At row2, column0:20-6*2-8*2=-8; column1:45-6*1-8*6=-9. Thus the canonical nonnegative production matrix hypothesis is false. This is an obstruction to that sufficient method, NOT a negative source minor.

## Bounded checks and exact gap

check.py: all minors of orders1..4 within indices0..6 in all six literal matrices, m2..8:123480 checks, no negatives and no zero square minors. Also1134 B collocation identities; production entries computed exactly with Fractions. These small checks are weaker than published evidence and have no discovery value.
reduction.py:1050 A/B collocation identities for m2,3,7,11,30, n0..20, k0,1,3,12,35; and800 seeded sparse square minors of orders2..8 with indices0..35, all positive. Sparse checks explore the reduction beyond the printed first-ten square, still no proof. Every helper used unchanged copied guard: AS and sampled process-group RSS512MiB, CPU210s, wall230s, nominal40ms scan interval, BLAS1. Guard peak for reduction about150MB. No cap increase.

Exact missing mathematical bridge: universal nonnegative minors for the four triangles, and universal strict collocation positivity for both c0 and c1. Strongest mathematical objection: the normalized kernels are not the printed Toeplitz/Hankel kernels and the natural production matrix is already signed. Strongest eligibility objection: later Fuss–Narayana/Riordan proof bodies have not been compared. Falsifier for the source: any exact negative triangle minor or nonpositive square minor at an allowed m and finite index tuples. Falsifier for coefficient-array strategy: a negative exact coefficient-array minor; even failure of that stronger strategy would not refute the source.

## Current public registry bounds

Read the actual root final-freeze CURRENT-REGISTRIES and full compressed inventories, with350197 Omega and174524 OpenAI entries at18:13:38Z, and r85 provenance/current delta limits. An initial API comparison failed404 because the supplied compact prompt had an extra leading a in the Omega hash; corrected using the actual r85 provenance, not a guessed branch. Correct comparison6f8ee6614e0faf9dfa2cce46d1eb758dea97c335 to current e9c949019b00eb22ab88e81d6ac6b1047925d95d returns13/13 commits and194 files, below250/300 bounds. OpenAI head remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Selected current Cigler problem body is read: it proves strip-series products for heights4m/4m+1, not this six-matrix statement. Do not equate its triage theorem badge with a Fuss–Narayana resolution. This body provides a concrete distinction, not clearance of every semantic alias. Content patches also screened; omitted/truncated patches and lack of whole-repository semantic audit remain limits. r85 provenance bridges the older final-freeze and r85 heads only to its documented bounded extent. No current-prior PASS is asserted.

All exact URLs, retrieval UTCs, HTTP errors, byte counts and hashes are in http.json and provenance.json. No PROOF.md was created because no full ordinary resolution exists. Count credit0.
''')
(L/'progress.md').write_text(f'''# Progress (UTC)

- 2026-10-29T18:43 onward: governing files and available r85/r86/r87 progress/context read; all-date filename-first duplicate gate.
- 18:46: three public-source screens; actual Narayana and Toeplitz bodies downloaded/read; spectral VoR challenge preserved and stopped.
- 18:46–18:48: current registry heads and bounded comparison; initial malformed-base404 corrected from actual r85 provenance. Closest UCL/Wiley bodies403, no retries.
- 18:47–18:49: exact full-parameter square reduction, failed signed-production route, bounded rational diagnostics. All mathematical and eligibility gaps retained.
- Finalized {now}: zero nomination/credit; no Lean/paper/PROOF or shared edits. Artifact hashes computed after report writes; finalizer's active stdout/guard excluded explicitly.
''')
(L/'run.sh').write_text('''#!/bin/sh
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py
python helper_guard.py python reduction.py
''')
# Provenance embeds all pre-existing artifacts after final substantive writes; cannot hash itself.
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['provenance.json','finalize.log','finalize-guard.json']}
p={'lane':str(L),'finalized_utc':now,'status':'UNRESOLVED_ZERO_NO_NOMINATION','discovery_count_credit':0,'counts_unchanged':{'additional':8,'total':38},'source':{'authors':['Yi Wang','Arthur L.B. Yang'],'title':'Total positivity of Narayana matrices','label':'Conjecture4.1','page':'8–9','date_in_body':'2017-11-07','url':json.loads((L/'http.json').read_text())[0]['url'],'scope':'every integer m>=2, four TP triangles and two STP squares, all finite minors'},'http':json.loads((L/'http.json').read_text()),'registry':json.loads((L/'registry-audit.json').read_text())['delta'],'access_limits':['spectral author PDF HTTP200 blocking HTML','UCL successor PDF403','Wiley successor full body403','initial malformed Omega comparison404; corrected from actual r85 provenance','bounded path/patch search is not semantic whole-repository audit'],'gap':'All-order four-triangle TP and two-square collocation STP remain unproved; successor primary-body comparison HOLD','strongest_objection':'Canonical production matrix signed at m2; ordinary source PF/Hankel reductions do not extend directly; later Riordan bodies unread','falsifier':'Allowed negative triangle minor or nonpositive square minor; negative coefficient-array minor defeats only stronger proposed route','guard':'unchanged copied improved helper_guard.py; AS/group RSS512MiB CPU210 wall230 nominal40ms BLAS1','manifest_sha256':manifest,'manifest_exclusions':{'provenance.json':'self-referential manifest','finalize.log':'actively written finalizer stdout','finalize-guard.json':'actively written finalizer guard telemetry'}}
(L/'provenance.json').write_text(json.dumps(p,indent=2));print('finalized',now,'artifacts',len(manifest))
