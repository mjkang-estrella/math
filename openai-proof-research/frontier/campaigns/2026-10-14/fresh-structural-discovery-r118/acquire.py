from pathlib import Path
import json,hashlib,urllib.request,subprocess,concurrent.futures
ROOT=Path(__file__).parent; PRIV=ROOT/'packet/private'; PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads(Path('sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
families={'126':'Exponential-PSD-rank-of-positively-shifted-matching','192':'Unbounded-Violations-of-the-Square-Root-Degree','185':'A-Counterexample-to-the-Infinite-Matroid','120':'Almost-Linear-Time-Maximum-Cardinality'}
paths=subprocess.run(['rg','--files','--hidden','sources/cache','frontier/sources','frontier/campaigns'],capture_output=True,text=True,check=True).stdout.splitlines()
selected=[]
for fam,s in families.items():
 for e in tree['tree']:
  if s not in e['path'] or not e['path'].endswith(('.tex','.bib')) or '/figures/' in e['path']:continue
  if fam=='120' and not any(x in e['path'] for x in ['01-introduction','03-matching-state','10-f-factors','references.bib']):continue
  selected.append((fam,e))
def get(item):
 fam,e=item; target=PRIV/'upstream'/fam/Path(e['path']).name;target.parent.mkdir(parents=True,exist_ok=True)
 origin=None;data=None
 for p in paths:
  if p.endswith(e['path'].split('/build/')[-1]) and Path(p).stat().st_size==e['size']:
   b=Path(p).read_bytes()
   if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']:data=b;origin=p;break
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
 if data is None:
  with urllib.request.urlopen(url,timeout=45) as r:data=r.read();origin='fresh HTTP '+str(r.status)
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
 target.write_bytes(data)
 return dict(family=fam,path=e['path'],git_blob=e['sha'],sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),url=url,origin=origin,local=str(target.relative_to(ROOT/'packet')))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:rows=list(ex.map(get,selected))
(PRIV/'upstream-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
(PRIV/'tree-receipt.json').write_text(json.dumps(dict(path='sources/preprints-tree.json',sha256=hashlib.sha256(Path('sources/preprints-tree.json').read_bytes()).hexdigest(),entries=len(tree['tree']),truncated=False,selected=[e for _,e in selected]),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),families={f:sum(r['family']==f for r in rows) for f in families},fresh_http=sum(r['origin'].startswith('fresh HTTP') for r in rows)),indent=2))
