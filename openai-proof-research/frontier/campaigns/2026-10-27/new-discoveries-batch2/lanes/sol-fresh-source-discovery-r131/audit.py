import json,re,gzip,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
hits=json.loads((L/'history-matches.json').read_text())
pat=re.compile(rb'2608[.]08692|2609[.]15784|weighted.bond|Schur.log.concav|hypergraph.burning|lazy.burning|2412[.]04389|2403[.]01001',re.I)
selected=[]
for j in hits:
 p=R/j['path'];b=p.read_bytes()
 if pat.search(b):
  excerpts=[]
  for i,line in enumerate(b.decode(errors='replace').splitlines(),1):
   if pat.search(line.encode()):excerpts.append([i,line[:1000]])
  selected.append(dict(path=j['path'],sha256=j['sha256'],matches=excerpts))
(L/'focused-history.json').write_text(json.dumps(selected,indent=2));print(json.dumps(selected,indent=2)[:22000])
print('focused',len(selected),'all matched bodies',len(hits))
j=json.loads((L/'sources/omega-delta.json').read_text())
out={k:j.get(k) for k in ['status','ahead_by','total_commits']};out.update(returned_commits=len(j.get('commits',[])),returned_files=len(j.get('files',[])),merge_base=j.get('merge_base_commit',{}).get('sha'),paths=[x['filename'] for x in j.get('files',[])],semantic_clearance=False)
(L/'registry-delta-receipt.json').write_text(json.dumps(out,indent=2));print(out)
