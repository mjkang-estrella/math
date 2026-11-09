from pathlib import Path
import json,hashlib,datetime,re
L=Path(__file__).resolve().parent;B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
refs=json.loads((L/'history-verified.json').read_text())
terms=['Leake','Ryder','annihilation','Mandrescu','Komisarski','Rajba','Koolen','Markowsky','Ciaurri','Roncal','Taranenko','branching-ruin','Randić','Hanson-Wright','planting trees','Balodis','connected induced subgraph','Berkowitz','1811.06382','1811.04722']
hits=[]
for r in refs:
 p=Path(r['path']);assert sha(p)==r['sha256'];s=p.read_text(errors='replace')
 for t in terms:
  if t.casefold() in s.casefold():
   i=s.casefold().index(t.casefold());hits.append(dict(term=t,path=str(p),sha256=r['sha256'],excerpt=s[max(0,i-100):i+400]))
(L/'alias-history.json').write_text(json.dumps(hits,indent=2))
bindings=[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
for r in bindings:assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy']))
(L/'source-postcheck.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),bindings_verified=len(bindings),immutable_history_verified=len(refs),administrative_policy='snapshot-only'),indent=2))
ids={p.stem for p in (L/'primary').glob('*.pdf')}
entries=json.loads((L/'slice.json').read_text())
selected=[d for d in entries if d['id'].split('/')[-1] in ids]
(L/'selected-chronology.json').write_text(json.dumps(selected,indent=2))
texts=[dict(path=str(p.relative_to(L)),sha256=sha(p)) for p in (L/'science').glob('*.txt')]
(L/'derived-text-bindings.json').write_text(json.dumps(texts,indent=2))
admin=[]
for p in (L/'admin').glob('*.json'):
 try:d=json.loads(p.read_text())
 except Exception:continue
 if isinstance(d,dict) and 'accepted' in d:
  admin.append(dict(snapshot=p.name,keys=list(d),accepted_titles=[r.get('title') for r in d['accepted']]))
(L/'administrative-read.json').write_text(json.dumps(admin,indent=2))
print(json.dumps(admin,indent=2))
provenance=dict(lane=str(L),date='2026-10-30',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',limits=dict(AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),counts=dict(additional=9,total=39,next=40,authority='root alone'),source_policy='Freeze response originals/copies and verify before extraction; verify again after reads. Derived texts are bound separately. Administrative snapshots only.',public_registry=dict(current_head=None,historical_pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',limitation='Denied routes parked; no live clearance'),manifest_excludes=['final-manifest.json','verification-receipt.json'],qualified_survivors=0)
(L/'provenance.json').write_text(json.dumps(provenance,indent=2))
files=[dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']]
(L/'final-manifest.json').write_text(json.dumps(dict(files=files),indent=2))
print('manifest',len(files),'sources',len(bindings),'alias hits',len(hits))
