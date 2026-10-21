import os,re,json,hashlib
from pathlib import Path
from isolation import ROOT,reason
query=re.compile(r'Potts|four.state|binary partition|Blackwell|boundary.{0,40}(?:coarsen|partition|partial)|quenched.{0,30}reconstruct',re.I)
out={'policy_sha256':hashlib.sha256((ROOT/'code/isolation.py').read_bytes()).hexdigest(),'query':query.pattern,'utf8':0,'nonutf8':0,'pruned':[],'errors':[],'hits':[]}
for base,dirs,files in os.walk('.',topdown=True,followlinks=False):
 b=Path(base)
 keep=[]
 for d in sorted(dirs):
  p=b/d; why=reason(p)
  if p.is_symlink(): why='symlink'
  if why: out['pruned'].append({'path':str(p),'reason':why})
  else: keep.append(d)
 dirs[:]=keep
 for f in sorted(files):
  p=b/f; why=reason(p)
  if p.is_symlink(): why='symlink'
  if why: out['pruned'].append({'path':str(p),'reason':why}); continue
  try: data=p.read_bytes(); s=data.decode('utf8')
  except UnicodeError: out['nonutf8']+=1; continue
  except OSError as e: out['errors'].append([str(p),str(e)]); continue
  out['utf8']+=1
  matches=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if query.search(line)]
  if matches: out['hits'].append({'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'matches':matches})
(ROOT/'private/history02.json').write_text(json.dumps(out,indent=2))
print({k:out[k] for k in ['utf8','nonutf8','errors']}); print('pruned',len(out['pruned']),'hit files',len(out['hits']))
for x in out['hits']:
 print(x['path'])
 print('matches',len(x['matches']))
