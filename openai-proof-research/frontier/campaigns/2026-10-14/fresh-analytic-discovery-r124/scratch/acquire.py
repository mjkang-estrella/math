import json,re,hashlib,urllib.request,concurrent.futures
from pathlib import Path
R=Path(__file__).resolve().parents[1]; P=R/'packet'; T=json.loads((P/'private/context/preprints-tree.json').read_text())
assert not T['truncated'] and len(T['tree'])==13223
S=(P/'private/context/CONTENTS.md').read_text();sel=[]
for n in ['084','149','228','263']:
 sec=re.search(r'\*\*'+n+r'\..*?(?=\*\*\d{3}\.|\Z)',S,re.S).group()
 dirs=[p.rsplit('/',1)[0] for p in re.findall(r'\]\((preprints/[^)]+\.pdf)\)',sec)]
 for e in T['tree']:
  if e['type']!='blob' or not e['path'].endswith(('.tex','.bib')) or '/figures/' in e['path']:continue
  if not any(e['path'].startswith(d+'/') for d in dirs):continue
  if n=='263' and 'Uniform-excess' in e['path'] and not any(z in e['path'] for z in ['introduction','screening','atomic-propagation','outer-radius','interfaces','references']):continue
  sel.append((n,e))
def get(pair):
 n,e=pair; url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path'];b=urllib.request.urlopen(url,timeout=45).read()
 assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
 p=P/'private/canonical'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return dict(family=n,path=e['path'],type=e['type'],blob=e['sha'],size=len(b),sha256=hashlib.sha256(b).hexdigest(),url=url,local=str(p.relative_to(P)))
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex: rows=list(ex.map(get,sel))
(P/'public/canonical.json').write_text(json.dumps(rows,indent=2)+'\n');print('authenticated',len(rows),'blobs',sum(x['size'] for x in rows),'bytes')
