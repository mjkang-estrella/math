import hashlib,json,subprocess
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-fresh-source-discovery-r117';B=r.parents[1];repo=B.parents[4]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
rows=[json.loads(l) for l in (s/'finalmanifest.jsonl').read_text().splitlines()]
for q in rows:assert sha(s/q['path'])==q['sha256'],q['path']
bef=json.loads((s/'frozen-before.json').read_text());aft=json.loads((s/'frozen-after.json').read_text())
bb={q['path']:q['sha256'] for q in bef};aa={q['path']:q['after_sha256'] for q in aft}
assert set(bb)==set(aa)
drift=[p for p in bb if bb[p]!=aa[p]]
assert drift==[str(B/'NEXT.md')],drift
for p,h in bb.items():
 if p not in drift:assert sha(Path(p))==h,p
local=json.loads((s/'sourcehashes-before.json').read_text())
assert local==json.loads((s/'sourcehashes-after.json').read_text())
for p,h in local.items():assert sha(s/p)==h,p
history={}
for commit in ['8ea6283938','3a6da5ab09']:
 data=subprocess.check_output(['git','show',commit+':'+str((B/'NEXT.md').relative_to(repo))],cwd=repo)
 history[commit]=hashlib.sha256(data).hexdigest()
assert history['8ea6283938']==bb[drift[0]]
assert history['3a6da5ab09']==aa[drift[0]]
(r/'checks.py').write_bytes((s/'checks.py').read_bytes())
o={'manifest_entries':len(rows),'mathematical_inputs_unchanged':True,'local_sources_unchanged':len(local),'worker_strict_freeze_status':'FAILED_HOLD_PRESERVED','drift':drift,'root_authorized_commit_hashes':history,'root_disposition':'No nominee. Shared mutable NEXT changed by root, not mathematical tampering.','credit':0,'counts':[8,38]}
(r/'ADOPTION.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
