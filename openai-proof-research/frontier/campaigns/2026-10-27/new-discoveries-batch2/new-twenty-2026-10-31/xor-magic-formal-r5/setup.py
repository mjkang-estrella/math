from pathlib import Path
import hashlib,json,shutil
r=Path(__file__).resolve().parent
spec={'xor-magic-formal-r4c':['formal','SUMMARY.md','GAPS.md','results.json','statement-correspondence.md','xor-magic-r4c-partial-source.zip'],'xor-magic-formal-r4b':['formal/'+x+'.lean' for x in ['ComplementBlocks','ComplementCharts','ComplementDecomposition','ComplementAudit','InterpAssembly','InterpConnectivity','InterpEndpoints','InterpFactors','InterpGraph','InterpSums']]+['SUMMARY.md','GAPS.md','results.json','xor-magic-r4b-source.zip'],'xor-magic-focused-r1':['PROOF.md'],'xor-magic-review-r1':['review.json','lean/ReviewControls.lean']}
files=[r.parent/'xor-magic-root-ruling-r1.json']
for lane,names in spec.items():
 for name in names:
  p=r.parent/lane/name
  files.extend(sorted(p.rglob('*.lean')) if p.is_dir() else [p])
manifest={str(p.relative_to(r.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'receipts').mkdir(exist_ok=True)
(r/'receipts/input-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
for p in files:
 q=r/'inputs'/p.relative_to(r.parent);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
(r/'formal').mkdir(exist_ok=True)
for p in (r/'inputs').rglob('*.lean'):
 if '/formal/' in str(p):
  q=r/'formal'/p.name
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copyfile(p,q)
for name in ['tools','negative']:
 shutil.copytree(r.parent/'xor-magic-formal-r4c'/name,r/name,dirs_exist_ok=True)
for name in ['dev.py','replay.py']:
 shutil.copyfile(r.parent/'xor-magic-formal-r4c'/name,r/name)
(r/'tmp').mkdir(exist_ok=True);(r/'logs').mkdir(exist_ok=True)
print(len(manifest),len(list((r/'formal').glob('*.lean'))))
