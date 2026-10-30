from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;R=L.parents[5]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
ledger=json.loads((L/'context-ledger.json').read_text());prior=json.loads((L/'context-prior-campaign-context.json').read_text())
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(L),counts={k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},prior_context_fields=list(prior),status='ZERO_COMPLETE_RESOLUTIONS',selected=['Lopez Pouso-Segura2025 Conjecture1','Lucardesi-Mazzoleni-Ruffini2023v3 Conjecture1.2'],primary_access='http.jsonl',failures='failures.json',screen='history-receipt.json plus early-screen.json/exact-early-screen.json/legendre-screen.json',novelty='HOLD bounded project freshness only; live registries unavailable; no full public prior clearance',scope='Solo research; writes only assigned lane; no browser/git/Lean/manuscript/external posting',guard='Unchanged inherited helper_guard.py',scientific_freeze='scientific-freeze.json',final_manifest='finalmanifest.json'))
save('primary-hashes.json',[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=h(p),qualification='Non-PDF cheeger-aam.pdf is preserved HTML login body' if p.name=='cheeger-aam.pdf' else 'Actual saved source or extraction') for p in sorted((L/'sources').iterdir()) if p.is_file()])
external={r[0]:r[1] for r in json.loads((L/'history-receipt.json').read_text())['records']}
for p,_ in json.loads((L/'history-receipt.json').read_text())['bases']:external[str(Path(p))]=h(Path(p))
for r in json.loads((L/'registry-screen.json').read_text())['records']:external[r['path']]=r['sha256']
for n in ['sources/upstream.json','sources/CONTENTS.md']:external[n]=h(R/n)
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';external[str(g)]=h(g)
save('external-scientific-freeze.json',dict(records=external,exclusions='Live administrative NEXT.md/ledger.json excluded; frozen context copies included in lane science. No scientific source exclusions. Conservative echo overinclusion.'))
receipts={'scientific-verification.json','manifest-verification.json'}
exclude=receipts|{'scientific-freeze.json','finalmanifest.json'}
records={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in exclude}
save('scientific-freeze.json',dict(records=records,exclusions=sorted(exclude),reason='Self and final-manifest/verification-receipt cycle exclusions only. Administrative context copies and all source bytes frozen.'))
records['scientific-freeze.json']=h(L/'scientific-freeze.json')
save('finalmanifest.json',dict(records=records,exclusions=['finalmanifest.json']+sorted(receipts),reason='Self and separately generated verification receipts only. No stdout files are created by verification.'))
print('Frozen scientific',len(records)-1,'manifest',len(records),'external',len(external))
