import pathlib,json,random,itertools,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]) if len(sys.argv)>1 else 30; seed=int(sys.argv[2]) if len(sys.argv)>2 else 221; key=f'onecrossing{n}-seed{seed}'; rng=random.Random(seed)
# Icosahedral sphere: two pentagonal rings with apexes.
faces=[]
for i in range(5):
 j=(i+1)%5
 faces.extend([(0,1+i,1+j),(11,6+i,6+j),(1+i,1+j,6+i),(1+j,6+i,6+j)])
faces={tuple(sorted(f)) for f in faces}
def edges(fs):
 inc={}
 for f in fs:
  for e in itertools.combinations(f,2):inc.setdefault(e,[]).append(f)
 return inc
def graph(fs):
 a=[set() for _ in range(max(max(f) for f in fs)+1)]
 for e in edges(fs):u,v=e;a[u].add(v);a[v].add(u)
 return a
def split(fs,e,w):
 inc=edges(fs);f,g=inc[e];u,v=e;x=next(z for z in f if z not in e);y=next(z for z in g if z not in e)
 return (fs-{f,g})|{tuple(sorted(t)) for t in [(u,x,w),(v,x,w),(u,y,w),(v,y,w)]}
for w in range(12,n):faces=split(faces,rng.choice(list(edges(faces))),w)
for step in range(100000):
 inc=edges(faces);a=graph(faces);cost=sum(max(0,5-len(s)) for s in a)
 if cost==0:break
 e=rng.choice(list(inc));u,v=e;f,g=inc[e];x=next(z for z in f if z not in e);y=next(z for z in g if z not in e)
 if y in a[x] or a[x]&a[y]!={u,v}:continue
 delta=sum(max(0,5-(len(a[z])+d))-max(0,5-len(a[z])) for z,d in [(u,-1),(v,-1),(x,1),(y,1)])
 if delta>0 and rng.random()>.001:continue
 faces=(faces-{f,g})|{tuple(sorted(t)) for t in [(u,x,y),(v,x,y)]}
a=graph(faces);inc=edges(faces);assert len(faces)==2*n-4 and all(len(z)==2 for z in inc.values());assert all(len(a[u]&a[v])==2 for u,v in inc)
print({'vertices':n,'faces':len(faces),'minimum_degree':min(map(len,a)),'steps':step},flush=True)
if min(map(len,a))<5:sys.exit(1)
# All 84 edge crossings combined as a single disjoint SAT conjunction: each must be 4-colourable.
clauses=[];cases=[]
for z,(e,fg) in enumerate(inc.items()):
 u,v=e;f,g=fg;x=next(t for t in f if t not in e);y=next(t for t in g if t not in e);base=z*(4*n)
 def var(i,c):return base+4*i+c+1
 for i in range(n):
  clauses.append([var(i,c) for c in range(4)])
  for c,d in itertools.combinations(range(4),2):clauses.append([-var(i,c),-var(i,d)])
 for p,q in list(inc)+[(x,y)]:
  for c in range(4):clauses.append([-var(p,c),-var(q,c)])
 cases.append({'edge':e,'added':[x,y]})
p=D/f'outputs/{key}.cnf'
with p.open('w') as f:
 f.write(f'p cnf {4*n*len(cases)} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
(D/f'outputs/{key}.json').write_text(json.dumps({'faces':sorted(faces),'cases':cases,'minimum_degree':min(map(len,a)),'seed':seed},indent=2))
