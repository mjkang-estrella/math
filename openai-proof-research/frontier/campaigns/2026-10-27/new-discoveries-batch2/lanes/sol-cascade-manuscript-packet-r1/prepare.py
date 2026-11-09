from pathlib import Path
import hashlib,json,shutil
b=Path(__file__).resolve().parent;l=b.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={}
for lane,manifest,key in [('root-cascade-formal-r1','integrated-core-hashes.json','sha256'),('root-cascade-rate-candidate-r1','review-freeze.json','hashes')]:
 d=l/lane;m=d/manifest;inputs[str(m)]=sha(m)
 for n,h in json.loads(m.read_text())[key].items():
  p=d/n;assert sha(p)==h,(p,sha(p),h);inputs[str(p)]=h
  dest=b/('formal/'+Path(n).name if lane=='root-cascade-formal-r1' and n.startswith('formal/') else 'inputs/'+lane+'/'+n)
  dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 shutil.copyfile(m,b/'inputs'/lane/manifest)
for lane,names in {'root-cascade-formal-r1':['ADOPTION.md'],'sol-cascade-rate-preliminary-review-r1':['review.md'],'sol-cascade-source-prior-review-r2':['review.md','provenance.json','http.json','search-log.json'],'sol-cascade-depth-rate-formal-r1':['SUMMARY.md'],'sol-cascade-source-tree-formal-r1':['SUMMARY.md'],'sol-cascade-selected-family-formal-r1':['SUMMARY.md'],'sol-cascade-kraft-summability-formal-r1':['SUMMARY.md']}.items():
 for n in names:
  p=l/lane/n;inputs[str(p)]=sha(p);d=b/'inputs'/lane/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,d)
for p in (l/'sol-cascade-source-prior-review-r2/sources').glob('*'):
 if p.is_file() and sha(p)=='d691c3a9935abf9e8a11f2cdfe09ed70cf28e287c6a739ba86a4a6283a06aa7e':
  inputs[str(p)]=sha(p);shutil.copyfile(p,b/'inputs/supplement.pdf')
for p in [l.parent/'AGENTS.md',l.parent/'ledger.json',l.parent/'prior-campaign-context.json',l.parents[4]/'AGENTS.md']:
 if p.exists():inputs[str(p)]=sha(p)
(b/'input-hashes-before.json').write_text(json.dumps(inputs,indent=2,sort_keys=True)+'\n')
shutil.copyfile(l/'root-gamma-level-complete-r3/pins.json',b/'pins.json')
