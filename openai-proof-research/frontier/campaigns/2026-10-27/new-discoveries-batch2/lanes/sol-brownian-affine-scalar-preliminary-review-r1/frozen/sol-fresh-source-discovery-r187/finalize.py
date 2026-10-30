from pathlib import Path
import json,hashlib,datetime,re,gzip
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,v):(L/n).write_text(json.dumps(v,indent=2)+'\n')
def write(n,s):(L/n).write_text(s)
pat=re.compile(r'2603[.-]27602|Dumaz|Magaldi|Brownian.*Affine|Affine.*Brownian|BoundaryMomentum|Sannipoli',re.I)
out=[]
base=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
for r in json.loads(base.read_text())['records']:
 p=Path(r['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 try:
  j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
 except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
 out.append(dict(path=str(p),sha256=sha(b),hits=hits))
save('registry-screen.json',dict(utc=now(),records=out,limits='Cached path screen only, no novelty clearance. Historical caps/missing merge trees PARKED. Current heads/bodies unavailable through denied GitHub routes. Current public github.io index blocked by local broad github-substring preflight assertion before network access; no response saved, no retry.'))
save('primary-hashes.json',[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted((L/'sources').iterdir())])
save('search-discovery-receipt.json',dict(utc=now(),method='Public web search tool for discovery only, plus three guarded Bing RSS probes whose bodies were irrelevant. Primary document retrieval/extraction/hash/check/edit scripts guarded. No browser. Web search response bodies not separately serialized; this is a provenance limitation.',query_groups=[['conjecture log concavity probability density2025','conjecture geometric inequality2025 integral convexity','conjecture complete monotonicity2025 probability'],['conjecture2025 integral monotonicity','Some isoperimetric inequalities involving the boundary momentum conjecture','conjecture probability Bessel2024/2025'],['On hitting times of affine boundaries Salminen Yor pdf','2603.27602 proof conjecture reflected Brownian','reflected Brownian negative drift affine hitting probability'],['Ruin probabilities in a two-dimensional setting pdf','Dumaz Magaldi conjecture matching2026','reflected Brownian affine boundary series drift'],['Grandits Drasin pdf','Mayerhofer2019 reflected Brownian hitting','2603.27602 author']],limits='Search snippets are leads, not proof bodies or novelty clearance. No claimed exhaustive specialist search.'))
write('SUMMARY.md','''# r187 — zero eligible nominations

Fresh project screen: 2,528 qualified scientific records, five changed/new, zero missing; inherited r111–113 originals retained. No echo exclusions. Two fresh source questions reached after reconnaissance; old/public/credited leads were not target slots.

Strongest route produced a complete ordinary proof of Dumaz–Magaldi arXiv:2603.27602v1 equation(6), for every a>=0,b>0,mu>0. See PROOF.md. Recommend ZERO credit under the explicit routine-classical-adaptation exclusion: a characteristic-root series and stopped reflected-diffusion martingale close the scalar formula. It does not prove their full joint point-process Conjecture1.4. Root owns this eligibility judgment.

Secondary: La Manna–Sannipoli's published2025 global boundary-momentum maximization question; actual latest arXiv and published bodies read. No full proof/counterexample; no new universal route closed. Not nominated.

Six symbolic identities and sixty exact rational coefficient/cancellation checks PASS; finite checks do not replace the proof. Actual primary bytes, UTC URLs/hashes/chronology, access limits, scientific freeze and separate manifest verification included. Same-model Grandits body and current registry coverage remain material prior-art gaps. No Lean/manuscript/shared/git/count edits or external messages/posts/uploads/browser. Counts9additional/39total,next40.
''')
write('discovery.md','''# r187 source discovery and scope adjudication

## Inputs and early exclusions

Read ancestor/batch AGENTS, ledger, prior-campaign-context and NEXT; full administrative bytes saved as context snapshots. Ancestor upstream revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; catalogue read for context only, no theorem inferred from summaries. Current ledger9additional/39total,next40. No administrative edit.

history-receipt.json unions r184/r183/r182/r181/r178/r170 records, refreshes actual bytes, retains r111–113 originals, and adds qualified SUMMARY/discovery/PROOF/review/DECISION files. 2,528 records, five changed/new, zero missing. No whole-lane/date or echo exclusions. Copies are conservatively retained with their provenance paths and content hashes; path absence is not novelty evidence. early-screen.json identified beta-content2503.22488/367740 BEFORE mathematical work; its original counterpart is 2026-10-26/new-discoveries/lanes/parent-beta-content/PROOF.md, which explicitly excludes it via the deterministic IMC2024 theorem. Source bytes fetched in the same early reconnaissance round are not a fresh slot. Broad search's Mills-ratio result is our credited family; entropy concavity2609.11418 is publicly refuted, not a candidate. No investment or retirement based solely on those snippets. Forbidden assigned families and active r185/r186 were left alone.

second-screen.json and brownian-early-screen.json precede target-body investment. Both have zero relevant project matches. exact-alias-screen.json strengthens these with DOI/arXiv/title/author/statement aliases and again has zero matches. These are bounded project freshness checks, not worldwide priority.

## Fresh source A: scalar affine crossing formula

Laure Dumaz and Hugo Magaldi, The spectrum of the stochastic Bessel operator at high temperature, arXiv2603.27602v1, sourcep8 equation(6). Latest live abs lists v1 submitted29March2026, PDF dated31March. Author's live publication list still lists it as a preprint. Actual bytes/hash in primary-hashes/http receipts. Sourcep3 defines Skorokhod reflection; sourcepp7–8 distinguishes the a=0 largest-point theorem, Conjecture1.4 joint matching for every a>=0, and the explicit scalar formula. Exact statement and all quantifiers appear in PROOF.md. a>=0,b>0,mu>0 are handled universally, including a=0 and nonintegral a/b. No integer-drift restriction or large-intercept-only replacement. Zero intercept is a separate degenerate certain event and not a convergent unregularized series endpoint.

The complete argument chooses the characteristic roots of b d/dh + (1/2)d²/dx²-a d/dx, pairs them to satisfy the reflecting condition, and recursively cancels the moving absorbing-boundary terms. Convergence on the entire stopped wedge and the terminal limit are proved, not numerically assumed. The formula is an explicitly conjectured source byproduct, but weaker than the full joint-law conjecture. Recommend no nomination under the user's routine-adaptation exclusion, rather than relabeling a scalar helper as a full point-process result. Strongest objection and complete classical-method bridge are in PROOF.md. No gap is hidden in a finite numerical check.

Closest primary bodies read EARLY: Salminen–Yor1012.2038v1 §§2–3, Doob wedge formula, Corollary5, Theorem9 and proof: driftless reflection/bridge method. It does not directly state the a>0 formula. Its published bibliographic record is DOI10.1007/s10998-011-5075-2, Periodica62(1)(2011)75–101; source2026 reference has different pages/issue, an uncredited bibliographic detail. Mayerhofer published Risks7(4)(2019)105 DOI10.3390/risks7040105 §2/Theorem1/proof gives the exact exponential-test-function/Neumann/stopped-Itô mechanism for fixed barriers. The extension is written completely in PROOF.md rather than merely invoked as classical. Neither read body alone is claimed to subsume the new formula verbatim.

Closest material companion: Magaldi2411.13972v1 (21Nov2024), actual primary diffusion construction pp5–7 and final material read. It develops the earlier reflected-diffusion high-temperature limit; no scalar series or independent-gap joint matching was located in its actual body. The 2026 paper adds the matching conjecture and scalar series, so the old limit theorem is not a public full resolution. Grandits, Ruin probabilities in a two-dimensional setting and the Drasin–Shea Theorem, DOI10.1080/03461238.2025.2587653, accepted6Nov2025/published2025 online,2026 volume, has exactly relevant affine-crossing §4. Its direct publisher returned403 once and was not retried; public search excerpts identify this as a mandatory unread body. No abstract/snippet-based retirement or novelty clearance. Could contain a more complete same-model answer; retain HOLD. No author message or access bypass.

## Fresh source B: global boundary-momentum maximum

Domenico Angelo La Manna and Rossano Sannipoli, Some isoperimetric inequalities involving the boundary momentum, latest arXiv2309.14191v3 (3April2025), actual Journal of Optimization Theory and Applications207(2025) published28July2025, DOI10.1007/s10957-025-02757-7. Published body obtained successfully and read: introduction functional(9), local Theorem1.4, existence Proposition4.5 and final§5 question(1). Both versions retain the question: for every dimension n>=2, are balls global maximizers among bounded open convex sets with nonempty interior of

 F(E)=|E|^((n-2)(n+1)) / P(E)^(n²-1)
        * inf_{x0 in R^n} integral_{boundary E}|x-x0|² dH^(n-1)?

The supremum would be F(B)=1/(n^(n²-2)*omega_n^(n-1)), with uniqueness if that is intended; the question itself asks global maximality. The source proves planar global maximality, existence in general dimensions, and local maximality for nearly spherical convex bodies. None is silently substituted for all convex bodies. A possible route is a volume/perimeter-controlled bound on the boundary covariance trace, then compactness plus local stability to exclude remote maximizers. Precise gap: no global inequality giving that covariance bound, and compactness plus strict local maximality alone cannot exclude a second remote maximum. Thus this is not a tractable completed universal route and is not recommended for investment. Source-supplied existence/local results are helpers, not a resolution. The published version removes the older threshold-sharpness open question and changes wording in another final question; these are not fresh corrections or candidates. No classical bridge proving the global statement was found.

## Bounded screen and limits

At least one genuinely new unresolved attributed source with a concrete universal route was reached; the strongest scalar route was sustained through a full ordinary proof, then rejected provisionally as routine/insufficient for the broader conjecture. No attempt to fill target slots using three old leads. Bounded broad screen covered log-concavity/entropy, special-function monotonicity, beta convex-hull content, reflected diffusions and geometric boundary momentum. Search-discovery-receipt records queries. Three guarded Bing RSS probes returned irrelevant YouTube/Honda/Dubai bodies, preserved as failed discovery evidence; no meaning inferred.

Inherited HTTP inventories were read and saved with original hashes; r181 arXiv-search429, author TLS failures, r184 login AAM and oversized AMS failures remain adverse history. No denied GitHub/API/raw/codeload/public diff, ScienceDirect, Google challenges, IEEE418, OpenReview403, d-nb429 or SSRN403 route retried. New publisher403 stopped. The public registry index response exceeded the10MB fixed read bound, leaving an empty AssertionError in the original receipt; no bytes saved, no capraise/retry. Cached11 registry inventories are hash-bound and name-screened in registry-screen.json. Names alone cannot clear a statement; current heads/body and merge-history coverage remain HOLD, historical caps/missing trees PARKED. No reconstruction loop. Search tool discovery calls were outside the Python helper; all direct primary retrievals/extraction/hash/check/edit scripts used the required guard. Search-response bodies were not separately captured, a limitation made explicit.

Result: zero eligible nominations; no claim of a new-to-literature theorem or worldwide priority. The complete uncredited formula proof is retained for root review, without launching Lean, a manuscript, or a further agent. Root alone owns review/investment/acceptance and any count change.
''')
write('progress.md',f'''# Progress receipt

Completed at {now()}.
Read required context and inherited adverse-access receipts; refreshed scientific identities before target selection. Broad screen reached two fresh source questions. Completed ordinary universal scalar crossing formula proof and exact algebra checks; recommend routine-adaptation exclusion. Published global geometric question remains unresolved with precise gap. Zero eligible nominations, no acceptance/count change. All source chronology, hashes and limits in discovery/provenance/HTTP receipts. No running process or child remains.
''')
write('run-checks.sh','''#!/bin/sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 "$(dirname "$0")/checks.py"
''')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('provenance.json',dict(utc=now(),lane=str(L),counts=dict(additional=9,total=39,next=40),eligible_nominations=0,ordinary_scalar_proof='PROOF.md',status='Zero credit recommended; routine classical adaptation; no full joint-process proof',guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_MiB=512,sampled_group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,caps_unchanged=True,limits='40ms sampled group RSS; unsampled transients not ruled out'),scientific_originals='history-receipt.json records',source_receipts='http.jsonl',search_receipts=['search.jsonl','search-discovery-receipt.json'],source_hashes='primary-hashes.json',external_actions=False,browser=False,git_operations=False,lean=False,manuscript=False,limits=['Grandits body403 unread','Current registry heads/body incomplete','No exhaustive MathSciNet/zbMATH audit','Ordinary proof not independently reviewed','No worldwide-priority claim']))
# Correct the ball normalization by direct substitution V=omega_n R^n, P=n omega_n R^(n-1).
p=L/'discovery.md';p.write_text(p.read_text().replace('omega_n^(n-1)','omega_n^n').replace('The public registry index response exceeded the10MB fixed read bound, leaving an empty AssertionError in the original receipt; no bytes saved, no capraise/retry.','The public github.io registry index was blocked by the helper\'s broad github-substring preflight assertion BEFORE network access, leaving an empty AssertionError in the original receipt; no response was fetched or saved and no retry was made. This was a local conservative filter, not a remote access denial or oversized response.'))
# Freeze the scientific content after final drafting; receipts are explicitly outside it.
excluded={'scientific-freeze.json','scientific-verification.json','finalmanifest.json','manifest-verification.json'}
rows=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
save('scientific-freeze.json',dict(utc=now(),records=rows,exclusions=sorted(excluded),external_originals='history-receipt.json records; live NEXT/ledger are mutable administrative snapshots only'))
print('Wrote scientific documents and freeze',len(rows),'files; cached registry inventories',len(out))
