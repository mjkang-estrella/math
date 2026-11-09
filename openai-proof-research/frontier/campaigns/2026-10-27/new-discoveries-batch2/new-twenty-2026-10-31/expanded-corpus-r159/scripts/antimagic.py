import pathlib,json,itertools,subprocess
D=pathlib.Path(__file__).resolve().parents[1];clauses=[];nv=0
def var():
 global nv
 nv+=1;return nv
def clause(*xs):clauses.append(list(xs))
zero=var();clause(-zero)
def gate(inputs,func):
 z=var()
 for vals in itertools.product([False,True],repeat=len(inputs)):
  clause(*[(-x if b else x) for x,b in zip(inputs,vals)],z if func(*vals) else -z)
 return z
def add(a,b):
 c=zero;out=[]
 for x,y in zip(a,b):
  z=gate([x,y,c],lambda a,b,c:a^b^c);n=gate([x,y,c],lambda a,b,c:(a+b+c)>=2);out.append(z);c=n
 clause(-c)
 return out
def distinct(a,b):
 zs=[gate([x,y],lambda a,b:a!=b) for x,y in zip(a,b)]
 clause(*zs)
edges=[]
for h in [0,8]:
 edges.extend((h+2*j,h+2*j+1) for j in range(3))
 edges.extend((h+j,h+x) for j in range(6) for x in [6,7])
labs=[[var() for _ in range(5)] for e in edges]
for bits in labs:clause(*bits);clause(*[-x for x in bits])
for a,b in itertools.combinations(labs,2):distinct(a,b)
weights=[[var() for _ in range(8)] for c in range(3)]
for a,b in itertools.combinations(weights,2):distinct(a,b)
colors=[[var() for _ in range(3)] for v in range(16)]
sums=[]
for v in range(16):
 clause(*colors[v])
 for x,y in itertools.combinations(colors[v],2):clause(-x,-y)
 total=[zero]*8
 for j,e in enumerate(edges):
  if v in e:total=add(total,labs[j]+[zero]*3)
 sums.append(total)
 for c in range(3):
  for x,y in zip(total,weights[c]):clause(-colors[v][c],-x,y);clause(-colors[v][c],x,-y)
for a,b in edges:
 for c in range(3):clause(-colors[a][c],-colors[b][c])
clause(colors[0][0]);clause(colors[1][1]);clause(colors[6][2])
p=D/'outputs/antimagic.cnf';p.write_text(f'p cnf {nv} {len(clauses)}\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
print('variables',nv,'clauses',len(clauses),flush=True)
with (D/'logs/antimagic-solver.log').open('w') as f:
 try:r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical',str(p)],stdout=f,stderr=subprocess.STDOUT,timeout=110);rc=r.returncode
 except subprocess.TimeoutExpired:rc='timeout'
out={'r':1,'s':1,'m':2,'edges':edges,'solver_exit':rc,'scope':'bitvector encoding of all bijective edge labels and 3 induced vertex sums'}
if rc==10:
 model={int(x) for l in (D/'logs/antimagic-solver.log').read_text().splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0}
 vals=[sum((1<<j) for j,x in enumerate(bits) if x in model) for bits in labs]
 vs=[sum(vals[j] for j,e in enumerate(edges) if v in e) for v in range(16)]
 out.update(labels=vals,vertex_sums=vs,verified=sorted(vals)==list(range(1,31)) and len(set(vs))==3 and all(vs[a]!=vs[b] for a,b in edges))
(D/'outputs/antimagic.json').write_text(json.dumps(out,indent=2))
print(out,flush=True)
