from pathlib import Path
import os,json,re
from isolation import excluded,OWN
R=Path(OWN)
terms=['kähler','kahler',r'k\"ahler','hartogs','bounded holomorphic','bounded-holomorphic','liouville property','representing densit','representing measure','ryll','wojtaszczyk','hedenmalm','source359','source 359','t359','homogeneous polynomial grid','root-of-unity extraction','phase separation','phases separate','legendre transform','tube transfer','complete intersection hilbert']
programs={'.py','.sh','.js','.ts','.mjs','.cjs','.ps1','.ipynb'}
stats={'dirs_pruned':0,'files_pruned':0,'programs_omitted':0,'symlinks':0,'utf8_read':0,'nonutf8':0}
hits=[]; admitted=[]
for current,dirs,files in os.walk('.',topdown=True,followlinks=False):
 d=Path(current)
 kept=[]
 for name in dirs:
  p=d/name
  if excluded(p): stats['dirs_pruned']+=1
  elif p.is_symlink(): stats['symlinks']+=1
  else: kept.append(name)
 dirs[:]=kept
 for name in files:
  p=d/name
  if excluded(p): stats['files_pruned']+=1;continue
  if p.is_symlink(): stats['symlinks']+=1;continue
  if p.suffix.casefold() in programs: stats['programs_omitted']+=1;continue
  b=p.read_bytes()
  try: s=b.decode('utf8')
  except UnicodeDecodeError: stats['nonutf8']+=1;continue
  stats['utf8_read']+=1;admitted.append(str(p))
  matching=[i+1 for i,line in enumerate(s.splitlines()) if any(t in line.casefold() for t in terms)]
  if matching: hits.append({'path':str(p),'lines':matching})
(R/'private/history/search-expanded.json').write_text(json.dumps({'terms':terms,'stats':stats,'hits':hits,'admitted':admitted},indent=2)+'\n')
print(json.dumps(stats));print(json.dumps(hits,indent=2))
