from pathlib import Path
import os,re,json,sys
sys.dont_write_bytecode=True
sys.path.insert(0,'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132')
from isolation import denied,OWN
root=Path('.'); stats=dict(pruned_dirs=0,pruned_files=0,utf8=0,binary=0,symlink=0);hits=[]
pat=re.compile(r'normalized[ -]volum|ordinary[ -]double[ -]point|volume[ -]gap|\bReeb\b|K[ -](?:semi|poly)stable|canonical interiority|adjoint lifting|same-dimensional slice|\bklt\b|Gorenstein|jet[ -]semigroup|stabilizer|Koll.r[ -]component',re.I)
for d,dirs,files in os.walk(root,topdown=True,followlinks=False):
 keep=[]
 for name in dirs:
  p=Path(d)/name
  if p.is_symlink(): stats['symlink']+=1;continue
  if denied(p): stats['pruned_dirs']+=1;continue
  keep.append(name)
 dirs[:]=keep
 for name in files:
  p=Path(d)/name
  if p.is_symlink(): stats['symlink']+=1;continue
  if denied(p) or p.suffix.casefold() in ('.py','.sh','.js','.mjs','.cjs','.ts'):stats['pruned_files']+=1;continue
  try:
   b=p.read_bytes()
   if b'\0' in b:stats['binary']+=1;continue
   s=b.decode('utf8')
  except UnicodeError:stats['binary']+=1;continue
  stats['utf8']+=1
  lines=s.splitlines();matched=[]
  for i,line in enumerate(lines):
   if pat.search(line): matched.append({'line':i+1,'text':line})
  if matched:hits.append({'path':p.as_posix(),'hits':matched})
out=Path(OWN)/'private/history/mechanism-hits.json';out.write_text(json.dumps({'stats':stats,'hits':hits},indent=2)+'\n')
print(json.dumps(stats));print('Matching files:',len(hits))
for x in hits:print(x['path'], 'lines',','.join(str(h['line']) for h in x['hits']))
