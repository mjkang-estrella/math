from pathlib import Path
import os,re,json,hashlib
from guard import blocked,OWN
root=Path('.')
out=Path(OWN)/'private/search'
query=re.compile(r'\bBarnette\b|\bPfaffian\b|paired[ -]states?|spoke[ -]circulation|forest[ -]state|double[ -]dimer|induced[ -]tree[ -]partition|prescribed.{0,35}(?:three.edge|Hamilton)|(?:cubic.{0,35}bipartite|bipartite.{0,35}cubic)',re.I)
records=[]; seen=[]; skipped=[]; pruned=[]
for current,dirs,files in os.walk(root,followlinks=False):
 rel=Path(current)
 dirs[:]=sorted(d for d in dirs if not blocked(rel/d) and not (rel/d).is_symlink())
 for f in sorted(files):
  p=rel/f
  if blocked(p) or p.is_symlink(): continue
  try:
   b=p.read_bytes(); s=b.decode('utf-8')
  except UnicodeDecodeError: skipped.append(str(p)); continue
  except OSError as e: skipped.append([str(p),str(e)]); continue
  seen.append(str(p)); hits=[i for i,l in enumerate(s.splitlines(),1) if query.search(l)]
  if hits: records.append(dict(path=str(p),lines=hits,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(out/'history-search.json').write_text(json.dumps(dict(query=query.pattern,decoded=seen,skipped=skipped,hits=records),indent=2)+'\n')
print('Decoded UTF8',len(seen),'skipped',len(skipped),'matching paths',len(records))
for r in records: print(r['path'],r['lines'])
