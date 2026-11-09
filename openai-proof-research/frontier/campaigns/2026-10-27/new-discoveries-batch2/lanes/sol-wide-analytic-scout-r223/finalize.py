from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,v): (L/n).write_text(v if isinstance(v,str) else json.dumps(v,indent=2))
versions={r['id'].rsplit('/',1)[-1]:r for r in json.loads((L/'chronology.json').read_text())}
out=[]
for p in sorted((L/'primary').glob('*.pdf')):
 f=json.loads(p.with_suffix('.freeze.json').read_text());t=p.with_suffix('.txt')
 assert sha(p)==f['pdf'] and sha(t)==f['text']
 out.append(dict(id=p.stem,url='https://arxiv.org/pdf/'+p.stem,pdf_sha256=sha(p),text_sha256=sha(t),bytes=p.stat().st_size,chronology=versions[p.stem],after_read_verified=True))
write('source-map.json',out)
write('SUMMARY.md','''# Research handoff

No complete source-question resolution. Counts stay 9 additional / 39 total / next40; root alone decides.

Fifteen frozen primary papers screened across several eras. Three ranked nominations comprise two surviving broad families, not three independent families. Most probabilistic/geometric sources already prove or refute their historical targets. No breadth padding with those public results.

The strongest fresh lead, exceptional cylinder-interval order monotonicity (Aktaş–Baricz2609.39008v1 Q2 p28), received sustained Wronskian/energy, singular-phase and bounded numerical investigation. An exact counterexample defeats the naive zero-motion bound, while the target remains unresolved. mechanisms.md states the exact all-parameter missing energy inequality and strongest classical bridge objection. No PROOF.md claiming a full theorem/counterexample.

SCOUTING.md supplies scoped rejections and ranked next steps. source-map.json/chronology.json record primary versions and hashes. history-screen.json reuses 1,532 hash-verified immutable references without copying their bodies. Exact runnable method-obstruction checks pass; floating checks have no proof status. FAILURES.md preserves the initial report freeze error and numerical overflow warning.

No forbidden access route, browser, shared/git/public/MathDB action, children, Lean or manuscript. Current full registry heads and comprehensive citing coverage remain unavailable; no novelty clearance claimed. See RUN.md for capped replay and verification-receipt.json for separate guarded final verification.
''')
write('FAILURES.md','''# Failures and limitations

1. Initial bounded native reads displayed r221 and Padé SCOUTING before freezing them. They were subsequently snapshotted and checked. This violates the requested order for those inherited reports and is not retroactively cured. All newly retrieved primary PDFs and their text were frozen before scientific reading. Some initial administrative cat output was truncated; guarded init subsequently parsed ledger and snapshotted context.
2. work.py diagnostic emitted RuntimeWarning: overflow encountered in scalar multiply at v*w<0. Forty rows completed. Root bracketing is floating/mesh-based and not certified complete. No scientific positivity claim depends on it. Retained original tool output plus this record; rerun warning is in diagnostic-stderr.txt.
3. pdftotext emitted font-type mismatch warnings during retrieval. Mathematical formulas were checked against neighboring identities in the extracted source where used; no perfect extraction assurance for every unreviewed page.
4. No HTTP403/429/challenge was encountered on the attempted arXiv endpoints. Previously denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google routes were not retried. This leaves current complete registry clearance unavailable. Old inaccessible intervals remain parked.
5. No universal proof of the energy-versus-boundary lemma, no differentiated uniform singular-phase remainder, no validated continuous counterexample to Q2. Numerical nonviolations and method counterexamples do not resolve it.
6. Only two surviving broad families after triage. Famous global BCC/Blaschke endpoints deferred absent a new mechanism. Original 1998/2000 references and complete multiplier citing literature unverified, so no expensive historical-family solving investment.
''')
write('progress.md','''# Final progress

Completed: ancestor/batch instruction and administrative snapshot read; required compact reports; 15 primary-paper retrievals/freeze/extractions; bounded current arXiv search/version queries; 1,532 immutable-history hash checks and object/author/identifier screen; compact rejection register; three provisional nominations in two families; sustained strongest-target analysis; exact method-obstruction check; 40 floating diagnostics. No caps raised.

Unresolved: Q2's quantified energy domination, original/current comprehensive prior coverage, multiplier endpoint, source Q1 curvature. No complete discovery, no acceptance/count change. Root may prioritize the energy inequality; do not repeat the disproved cprime<c/mu shortcut.
''')
write('RUN.md','''# Capped runnable checks

From the lane directory, prefix every Python command with:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`

Then `python check_exact.py` for the exact rational comparisons, or `python work.py diagnostic` for bounded floating diagnostics. The guard fixes AS/groupRSS512MiB, CPU210s and wall230s; no cap raises. Retrieval commands in work.py are bounded and only target arXiv API/PDF endpoints. Do not rerun denied routes.

After all writes, `python finalize.py` builds manifest.json excluding itself and verification-receipt.json from its contents (the finalizer script IS included); then separately run `python verify.py`. No file other than verification-receipt.json should be written after manifest creation. Administrative snapshots are verified as saved snapshots only. Reused immutable history copies are verified against inherited fixed hashes, with originals compared when present.
''')
write('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(L),source_map='source-map.json',administrative='freeze.json',history='history-screen.json',new_primary_freeze_before_read=True,inherited_report_order_failure=True,counts=dict(additional=9,total=39,next=40),access='Only arXiv PDF/API; forbidden routes not attempted; registry-head gap remains',scientific_claim='unresolved, exact obstruction to a method only',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'))
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
write('manifest.json',dict(sha256=files,excludes=['manifest.json','verification-receipt.json']))
print(json.dumps({'files':len(files),'primary':len(out),'status':'manifest created; separate verification required'}))
