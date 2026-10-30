import sympy as s,json,hashlib,gzip,re
from pathlib import Path
L=Path(__file__).resolve().parent
r,t=s.symbols('r t',positive=True); F=r**2/(r+1)**3
K=s.factor(4*F**2/r**4+4*s.diff(F,r)**2/r**2+s.diff(F,r,2)**2)
P=s.apart(K,r); print('K',K,'partial fractions',P)
print('K inverse',s.inverse_laplace_transform(K,r,t))
for n in ['omega-head.json','openai-head.json']:
 j=json.loads((L/'sources'/n).read_bytes()); print(n,j['sha'],j['commit']['committer']['date'])
pat=re.compile(rb'black.hole|almasi|moradpour|shahbazi|2503.17880|kretschmann|entropy.bound|natural.measure',re.I);out=[]
for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
 p=L.parent/'root-edge-irregulator-final-freeze-r1'/n;hits=[]
 with gzip.open(p,'rb') as f:
  for b in f:
   if pat.search(b):hits.append(b.decode().strip())
 out.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),hits=hits))
(L/'registry-paths.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
