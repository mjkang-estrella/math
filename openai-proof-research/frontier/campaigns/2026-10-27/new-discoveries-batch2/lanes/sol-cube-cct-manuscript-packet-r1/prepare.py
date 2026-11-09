from pathlib import Path
import json,shutil,hashlib
L=Path(__file__).resolve().parent;P=L/'packet';E=P/'evidence';E.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
shutil.copyfile(G,P/'helper_guard.py')
for n in ['ledger.json','prior-campaign-context.json']:
 a=json.loads((L/'administrative'/n).read_text());print(n,'read in full',len(json.dumps(a)),'characters')
for n in ['Audit.log','Finite.log','Cube.log','Endpoint.log','replay-receipt.json','Finite.guard.json','Cube.guard.json','Endpoint.guard.json','Audit.guard.json']:
 shutil.copyfile(P/'formal'/n,E/n)
for n in ['marker.log','marker-node24.log','FAILURES.md']:
 shutil.copyfile(L/n,E/n)
for lane,name in [('sol-cube-cct-preliminary-review-r1','review.md'),('sol-cube-cct-formal-prior-review-r2','review.md'),('sol-cube-cct-source-formal-r1','SUMMARY.md'),('root-cube-cct-extracted-replay-r1','ROOT-REPLAY-RECEIPT.json')]:
 shutil.copyfile(L/'frozen'/lane/name,E/(lane+'-'+name))
for lane,sub,base in [('sol-cube-cct-preliminary-review-r1','primary','published'),('sol-cube-cct-preliminary-review-r1','primary','kocay'),('sol-cube-cct-formal-prior-review-r2','prior','set-reconstruction'),('sol-cube-cct-formal-prior-review-r2','prior','sceneries')]:
 for p in (L/'frozen'/lane/sub).glob(base+'.*'):
  if p.suffix in ['.pdf','.txt','.json']:shutil.copyfile(p,E/p.name)
shutil.copyfile(L/'freeze.json',P/'PROVENANCE.json')
(P/'output/pdf').mkdir(parents=True,exist_ok=True)
(P/'output/pdf/PDF-BLOCKED.txt').write_text('PDF BLOCKED: mandatory marker failed under AS512MiB twice. No authoring or visual QA performed. See evidence/marker*.log and evidence/FAILURES.md. Manuscript source is ../../manuscript.md.\n')
print('Evidence prepared; formal compiled files retained outside future package list.')
