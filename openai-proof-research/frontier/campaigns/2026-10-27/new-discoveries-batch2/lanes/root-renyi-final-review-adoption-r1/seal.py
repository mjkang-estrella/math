import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-renyi-threshold-full-final-review-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
f=json.loads((r.parent/'root-renyi-final-review-freeze-r1/freeze.json').read_text())
for n,h in f['files'].items():assert sha(Path(f['root'])/n)==h,n
d=json.loads((s/'rebuild/receipt.json').read_text());assert d['declarations']==104 and d['modules']==11
assert d['paper_sha256']=='44506a1d71a405c7a8bedab38ce51d7ed4ae08fd9a22d2013d3fab52a90bbe83'
assert d['packet_sha256']=='8e334cd5702319a79e9001e179ae8211b818100a4f1db4b440a6f93be3a9d555'
files={}
for p in sorted(s.rglob('*')):
 if not p.is_file() or '__pycache__' in p.parts:continue
 if p.name.endswith(('.pyc','.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so')):continue
 files[str(p.relative_to(s))]=sha(p)
(r/'review-freeze.json').write_text(json.dumps({'root':str(s),'files':files},indent=2)+'\n')
o={'review_files_frozen':len(files),'candidate_files_reverified':len(f['files']),'review_sha256':sha(s/'review.md'),'formal_declarations':104,'disposition':'HOLD_CURRENT_CAPPED_DELTA_ONLY_PLUS_DISCLOSED_INSTRUMENTATION_QUALIFICATION','credit':0,'counts':[8,38]}
(r/'ADOPTION.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
