import os,re,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
from isolation import ROOT,OWN,excluded,tests
assert tests()
base=ROOT/OWN
# Words and primitive aliases, not case-insensitive asymptotic notation.
pat=re.compile(r'ergodic|wiener.{0,8}wintner|return.{0,8}times|furstenberg|bourgain|sated|distal|multiple.{0,8}mixing|rokhlin|tensor.{0,8}packing',re.I)
hits=[];counts=dict(pruned_dirs=0,pruned_files=0,utf8=0,non_utf8=0,symlinks=0)
for here,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
 dirs.sort();files.sort();keep=[]
 for name in dirs:
  p=Path(here)/name
  if p.is_symlink():counts['symlinks']+=1;continue
  if excluded(p.relative_to(ROOT)):counts['pruned_dirs']+=1;continue
  keep.append(name)
 dirs[:]=keep
 for name in files:
  p=Path(here)/name
  if p.is_symlink():counts['symlinks']+=1;continue
  rel=p.relative_to(ROOT)
  if excluded(rel):counts['pruned_files']+=1;continue
  try:s=p.read_bytes().decode('utf8')
  except UnicodeDecodeError:counts['non_utf8']+=1;continue
  counts['utf8']+=1
  ms=[{'line':i,'token':m.group(0)} for i,line in enumerate(s.splitlines(),1) if (m:=pat.search(line))]
  if ms:hits.append({'path':str(rel),'matches':ms})
(base/'private/history/search-hits.json').write_text(json.dumps(hits,indent=2))
(base/'private/history/search-counts.json').write_text(json.dumps(counts,indent=2))
print(counts)
for x in hits:print(x['path'],[(a['line'],a['token']) for a in x['matches']])
