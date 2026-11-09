from pathlib import Path
import json,hashlib,tarfile
O=Path(__file__).resolve().parent

def edges(m,n):
 return {(u,v) for u in range(m*n) for v in range(u+1,m*n) if (u//n==v//n and (u%n-v%n)%n in (1,n-1)) or (u%n==v%n and (u//n-v//n)%m in (1,m-1))}
def check(m,n,parts,weights):
 E=edges(m,n);remaining=set(E);trace=[]
 assert len(parts)==len(weights)==5
 assert all(sum(v in e for e in E)==4 for v in range(m*n))
 for i,(part,w) in enumerate(zip(parts,weights),1):
  M={tuple(sorted(e)) for e in part};assert M and len(M)==len(part) and M<=remaining
  vertices=[v for e in M for v in e];assert len(set(vertices))==len(vertices)
  assert len(w)==m*n
  signs={f'{u}-{v}':w[u]+w[v] for u,v in sorted(remaining)}
  assert all(w[u]+w[v]==1 for u,v in M)
  assert all(w[u]+w[v]<0 for u,v in remaining-M)
  trace.append(dict(stage=i,matching_size=len(M),residual_edges=len(remaining),sums=signs,other_max=max((w[u]+w[v] for u,v in remaining-M),default=None)))
  remaining-=M
 assert not remaining
 return dict(m=m,n=n,vertices=m*n,edges=len(E),status='PASS',stages=trace)
d=json.loads((O/'evidence/discovery/outputs/pmd-certificate.json').read_text())
assert set(map(tuple,d['edges']))==edges(3,4)
checks=[check(3,4,d['layers'],d['weights'])]
for n in [5,6,7]:
 d=json.loads((O/f'certificates/3-{n}.json').read_text());checks.append(check(3,n,[s['matching'] for s in d['stages']],[s['weights'] for s in d['stages']]))
packet=O/'lean-packet.tar.gz';assert hashlib.sha256(packet.read_bytes()).hexdigest()=='f8e94288a8ab8a1ec5a8c41c1da1795e9bade7a06c44080aef9b883ab210c2de'
with tarfile.open(packet) as t:
 for x in t:
  assert not Path(x.name).is_absolute() and '..' not in Path(x.name).parts and (x.isfile() or x.isdir())
(O/'receipts/arithmetic.json').write_text(json.dumps(checks,indent=2)+'\n')
print('PASS: all four complete partitions and all residual integer inequalities; packet hash and safe member types.')
