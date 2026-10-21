import os,re,json,hashlib
from isolation import ROOT,OWN,exclusion
terms=re.compile(r'\bimmersions?\b|splitting[- ]off|edge[- ]disjoint paths|rooted clique|complete bipartite',re.I)
rows=[];excluded=[];binary=[];errors=[];hits=[]
for base,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
 dirs.sort();files.sort(); kept=[]
 for name in dirs:
  p=__import__('pathlib').Path(base)/name;why=exclusion(p)
  if p.is_symlink():why='symlink'
  if why:excluded.append({'path':str(p.relative_to(ROOT)),'reason':why})
  else:kept.append(name)
 dirs[:]=kept
 for name in files:
  p=__import__('pathlib').Path(base)/name;why=exclusion(p)
  if p.is_symlink():why='symlink'
  if why:excluded.append({'path':str(p.relative_to(ROOT)),'reason':why});continue
  try:b=p.read_bytes();s=b.decode('utf8')
  except UnicodeDecodeError:binary.append(str(p.relative_to(ROOT)));continue
  except Exception as e:errors.append([str(p.relative_to(ROOT)),str(e)]);continue
  ident={'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};rows.append(ident)
  found=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if terms.search(line)]
  if found:hits.append({**ident,'matches':found})
result={'policy_sha256':hashlib.sha256((OWN/'code/isolation.py').read_bytes()).hexdigest(),'eligible':rows,'excluded':excluded,'nonutf8':binary,'errors':errors,'hits':hits}
(OWN/'private/history/scan01.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'eligible':len(rows),'excluded':len(excluded),'nonutf8':len(binary),'errors':errors,'hits':[{'path':h['path'],'lines':[m['line'] for m in h['matches']]} for h in hits]},indent=2))
