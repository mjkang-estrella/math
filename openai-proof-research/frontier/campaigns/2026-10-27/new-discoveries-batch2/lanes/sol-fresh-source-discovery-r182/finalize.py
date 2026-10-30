import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(guard),sha256=sha(guard.read_bytes()),limits='unchanged512MiB AS/group sampled RSS, CPU210, wall230; environment thread limits1'))
save('primary-hashes.json',[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted((L/'sources').iterdir())])
save('provenance.json',dict(utc=now,lane=str(L),status='One fresh unresolved question; zero complete substantive source resolutions',counts='9additional/39total,next40; unchanged',target=dict(authors=['Neranga Fernando','Bhitali Kousik'],title='A further study of polynomial g_{n,q} over finite fields',doi='10.48550/arXiv.2606.01037',arxiv='2606.01037v1',statement='Question6.2; every integer e>2; classify permutation of F_(4^e)',chronology='Only v1 listed on current primary landing page, submitted2026-05-31T06:04:17Z; no authenticated journal body',decision='UNRESOLVED, full odd-e existence/classification gap; novelty HOLD'),companions=[dict(arxiv='1208.2942v1',journal='FFA22(2013)122–158',read='Theorems6.10–6.12 proofs, Lemma6.13, table'),dict(arxiv='1503.03162v1',journal='FFA37(2016)14–27',read='Theorem1.1, Theorem2.1/proof, Proposition3.1/proof, applications/table')],routine_exclusion='Conjecture5.23 complete classical convolution bridge in discovery.md; no credit',receipts=['http.jsonl','primary-hashes.json','search-receipt.json','history-receipt.json','original-copy-provenance.json','registry-screen.json'],prior_limits='No current registry HEAD clearance or authenticated journal bodies. Historical capped intervals/missing merge trees PARKED. Actual cached trees screened; names not novelty evidence. Denied routes not retried.',failures='One404 unused classical-note URL; no helper/resource failure. Initial wrapper-only registry scan recognized as inadequate and replaced before any novelty conclusion.',freeze_policy='Scientific originals/copies and authored analysis frozen; mutable live NEXT/ledger/prior context are represented only by archived snapshots. No live administrative comparison.'))
receipts=['scientific-verification.json','manifest-verification.json','verification.log','verification.guard.json']
manifest_excluded=['finalmanifest.json']+receipts
science_excluded=manifest_excluded+['scientific-freeze.json']
files=[p for p in L.rglob('*') if p.is_file()]
scientific=[p for p in files if str(p.relative_to(L)) not in science_excluded and not p.name.startswith('context-')]
save('scientific-freeze.json',dict(utc=now,exclusions=science_excluded,administrative_snapshot_rule='context-* omitted from scientific set but covered by final manifest; live shared files not checked',records=[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(scientific)]))
files=[p for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in manifest_excluded]
save('finalmanifest.json',dict(utc=now,exclusions=manifest_excluded,reason='Manifest excludes itself and subsequent verification receipts/logs to avoid self-reference; all other lane files included',records=[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(files)]))
print('freeze',len(scientific),'manifest',len(files))
