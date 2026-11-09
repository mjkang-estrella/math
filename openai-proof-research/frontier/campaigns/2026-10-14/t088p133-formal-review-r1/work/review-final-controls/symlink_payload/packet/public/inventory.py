"""Read-only named binding inventory. Original review code, MIT, 2026 Myeongjin Kang."""
import hashlib,json,stat
from pathlib import Path
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
BASE='frontier/campaigns/2026-10-14/'
ROOTS=[BASE+x for x in ['fresh-analytic-discovery-r133','t088p133-proof-r3','t088p133-formal-v1']]
FILES=['AGENTS.md','sources/upstream.json','frontier/NEW-TEN-2026-10-14.md']+[BASE+'discovery-analytic-r133-parent/'+x for x in ['formal-r1-intake/intake.json','formal-r1-intake/replay.py','formal-r1-intake/replay.json','formal-r1-disposition.md','proof-r3-disposition.md','proof-r3-adoption/adoption.json','formal-review-r1-brief.txt','formal-review-r1-dispatch.json']]
def record(p):
 s=p.lstat(); r={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':'dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link'}
 if r['kind']=='file': r.update(bytes=s.st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 if r['kind']=='link':r['target']=str(p.readlink())
 return r
def snapshot():
 entries={}
 for rel in ROOTS:
  p=PROJECT/rel
  for q in [p,*sorted(p.rglob('*'))]: entries[str(q.relative_to(PROJECT))]=record(q)
 for rel in FILES:
  p=PROJECT/rel
  if p.exists(): entries[rel]=record(p)
 return {'complete_roots':ROOTS,'fixed_files':FILES,'entries':entries}
if __name__=='__main__':print(json.dumps(snapshot(),indent=2,sort_keys=True))
