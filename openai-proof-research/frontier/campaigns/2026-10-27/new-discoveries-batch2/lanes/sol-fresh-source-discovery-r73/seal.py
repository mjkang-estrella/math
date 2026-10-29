from pathlib import Path
import json,hashlib,datetime
r=Path(__file__).resolve().parent;b=r.parent.parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(r/'sources/sun-web-evidence.md').write_text('''# Primary public-web evidence (transcription, not raw HTML)
URL: https://oeis.org/A390107/internal
Read in this lane on 2026-10-29; precise web-request timestamps unavailable.
Author: Zhi-Wei Sun, 2025-10-25. Internal revision #20: 2025-10-29 00:58:59.
Source definition: least positive m with gcd(m(n-1)+1, binom(m n²,m n))=1.
Source conjecture: a(n)<=sqrt(3n+4) for all n>0.
Source reports verification through n=30000 and links He–Yuan2024 and Sun2012.
Read via web open; direct urllib GET returned403, not retried. Hash in provenance
is of THIS transcription, not the remote response. Search-engine/web caches do
not establish that the entry has not changed since their crawl.
''')
(r/'sources/screen-evidence.md').write_text('''# Deferred/closed screens
Amiri https://arxiv.org/html/2511.08320v2 — actual retained primary body.
Conjecture1.1: equal-order finite abelian groups with equal sum of element orders
are isomorphic. Theorem1.4 explicitly gives this as one of four equivalent
conditions; Theorem1.3 supplies the LCM-group same-order-type bridge.
Live abs submission history latest observed v2 2026-05-09, original2025-11-11.
No independent correctness audit; source already publicly claims full resolution.

Tian source: https://www.mdpi.com/2227-7390/14/1/127
DOI https://doi.org/10.3390/math14010127
Primary indexed abstract advertises positive-exponent support and at-most-m
solutions for fixed m primes; actual web open429, no retry or alternate-host
attempt. Closest theorem bodies and exact conjecture label UNREAD. DEFER.
These are paraphrases of tool-visible source/search evidence, not raw archives.
''')
(r/'failures.md').write_text('''# Failures and limits
- Publisher actual Tian article web open: HTTP429. No retry/bypass; deferred.
- OEIS direct urllib request403; primary page had already been read via web tool.
  No retry after the403. Transcription labelled separately from raw evidence.
- Guessed unrelated teorth/ai-math README URL404. Wrong repository, no evidence.
  Correct inherited Omega repository URL subsequently used; no API calls.
- Initial routes.py expected p3 carries at9 AND27 for n8,m2. Assertion caught it;
  direct floor calculation gives only9. Failed source retained as
  logs/routes-initial-failed.py; successful corrected suite retained. First guard
  exit1, peak28151808 bytes, wall0.15623s (tool output transcribed here).
- Initial setup/fetch/pdftotext guard receipts were visible in tool output rather
  than redirected to disk. Metadata setup peak78835712/wall1.69062/exit0,
  fetch25247744/1.82192/exit0, text14135296/0.05151/exit0. No cap deviations.
- No inherited API reset evidence; no API retry, no current-HEAD identification.
  Live raw README is not a complete tree. Dated lexical tree screens incomplete
  as a current/global novelty screen. MathDB not queried or used as clearance.
- No full mathematical result; all checked ranges remain finite.
''')
checks=json.loads((r/'checks.json').read_text());routes=json.loads((r/'route-checks.json').read_text())
(r/'SUMMARY.md').write_text('''# r73 — full Sun binomial-coprimality bound unresolved; credit0

Three fresh expert-source questions screened: Amiri already publicly resolves
Tărnăuceanu's same-order abelian-group psi conjecture; Tian triangular support
question deferred on publisher429; selected Sun OEIS A390107, EVERY n>=1 admits
m<=floor(sqrt(3n+4)) with gcd(m(n-1)+1,binom(mn²,mn))=1. Actual primary page and
closest He–Yuan2024 theorem/Remark/proof bodies read early. Older summary screen
414 files found no matching source; no accepted-family variant pursued.

Exact carry criterion and necessary gcd(n,m-1)=1 proved. Complete prime-modulus
criterion: for n,m>=2 and d=m(n-1)+1 prime, success iff m<=n. But n20 has no
prime modulus within the source bound; higher-power carries at n8,m2 invalidate
checking only prime powers dividing d. These are method failures, NOT source
counterexamples. Missing uniform short-menu carry-avoidance lemma remains.

run.sh PASS:1600 literal-binomial comparisons, all n1..100000 least-m scans,
171294 sufficient-prime tests,6749 complete prime-modulus equivalences, and
full local carry certificate a32=10. No universal proof from finite evidence.
All scripts use unchanged AS/groupRSS512MiB,CPU210/wall230,40ms,BLAS1 guard.
One expected-carry assertion mistake corrected; failed source preserved.

Actual pinned Omega coprime-divisor-tuples claim and Lean proof read: different
OEIS count, no binomial carry endpoint. Live dev README fetched, current registry
HEAD/delta remains HOLD. No API403/429 retry/bypass; observed6c27... at15:49 is
NOT currentHEAD. r57 Blueprint D5 distinguished from actual Lean D5. URLs,
versions, hashes, UTC/access gaps and runnable exact checks retained.

No full ordinary source resolution, PROOF.md, Lean, paper or nomination.
All helpers/finite cases are routine classical consequences and uncredited.
Root counts7additional/37total unchanged. Solo, assigned-lane-only; no children,
git/shared/other-lane edits, browser/account/contact/upload/post actions.
''')
(r/'progress.md').write_text(f'''# Progress — {now}

Read/reconciled ancestor/batch rules, ledger/prior context/NEXT, recent r57–r71,
and r72 overlap summary. Cached old-summary search preceded selection. Three
source screens completed; two retired/deferred before investment. Primary and
closest source statements checked before arithmetic work. Current public searches
and cached named registry scopes checked early; no full registry freshness claim.

Completed ordinary helper analysis: carry equivalence, gcd necessary condition,
prime-modulus iff. Two explicit shortcut obstructions and full n32 instance.
Exact bounded suites pass; no full endpoint. Strongest remaining lemma/falsifier
and classical-bridge risk in discovery.md. Scope/novelty/access HOLD retained.
No Lean or manuscript investment, no acceptance/count update.

Validation: sh run.sh (offline). See logs/exact-guard.json and
logs/routes-guard.json. All computations exact; finite ranges are not proofs.
No cap increase. Failures and preliminary guard receipt transcription in
failures.md. Metadata/file operations also run under copied guard where scripted.
''')
contexts=[]
for p in [b/'AGENTS.md',b/'ledger.json',b/'prior-campaign-context.json',b/'NEXT.md',b.parents[3]/'AGENTS.md']:
 contexts.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
for n in range(57,73):
 p=r.parent/f'sol-fresh-source-discovery-r{n}'/'SUMMARY.md'
 if p.exists():contexts.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
prov={'lane':'sol-fresh-source-discovery-r73','sealed_utc':now,'status':'UNRESOLVED; credit0','scope':'Sun A390107 entire n>=1 bound','contexts':contexts,'http':json.loads((r/'sources/fetch.json').read_text())+json.loads((r/'sources/fetch-claims.json').read_text()),'live_registry':json.loads((r/'registry-live.json').read_text()),'web_evidence':[{'url':'https://oeis.org/A390107/internal','date_utc':'2026-10-29','status':'public web reader succeeded; raw urllib403; precise web request timestamp unavailable','version':'internal #20 2025-10-29; authored2025-10-25','artifact':'sources/sun-web-evidence.md','raw_response_hash':None},{'url':'https://www.mdpi.com/2227-7390/14/1/127','date_utc':'2026-10-29','status':'web open429; no retry','version':'published2025-12-29, Mathematics2026 14(1)127; actual body unread','raw_response_hash':None}], 'searches':{'date_utc':'2026-10-29','queries':['"A390107" proof conjecture','"Sun" "relatively prime" "sqrt" "binomial" 2025','site:github.com "A390107"','site:github.com/the-omega-institute/trureturing "binomial" "coprime"','site:github.com/openai/math "binomial" "divisibility" Sun'],'scope':'public web results only; no absence inference; no complete/current registry claim'},'registry_limits':{'latest_observed_omega':'6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3','observed_utc':'2026-10-29T15:49:00Z (inherited approximate minute)','is_current_head':False,'api_calls':0,'no_reset_evidence':True,'r57_D5_kind':'Blueprint markdown; not actual Lean','actual_matched_claim':'Wiseman A062319 divisor tuple count; entire actual .lean body read; not replayed','freshness':'HOLD'},'resource_caps':{'address_space_bytes':536870912,'sampled_group_rss_bytes':536870912,'cpu_seconds':210,'wall_seconds':230,'sampling_ms':40,'blas_threads':1,'guard_origin':'r71/capped_run.py copied byte-identical'},'full_ordinary_proof':False,'formal_or_paper_work':False,'external_mutations':False,'file_hashes':{}}
for p in sorted(r.rglob('*')):
 if p.is_file() and p.name!='provenance.json':prov['file_hashes'][str(p.relative_to(r))]=hashlib.sha256(p.read_bytes()).hexdigest()
(r/'provenance.json').write_text(json.dumps(prov,indent=2))
print('sealed',now,'files',len(prov['file_hashes']))
