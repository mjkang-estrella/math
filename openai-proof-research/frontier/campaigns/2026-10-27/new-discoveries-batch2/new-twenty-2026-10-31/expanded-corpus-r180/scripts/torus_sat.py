import pathlib,json,itertools as it,sys
D=pathlib.Path(__file__).resolve().parents[1];n,m=map(int,sys.argv[1:3]);edges=set()
for i in range(n):
 for j in range(m):
  v=i*m+j
  edges.add(tuple(sorted((v,((i+1)%n)*m+j))));edges.add(tuple(sorted((v,i*m+(j+1)%m))))
edges=sorted(edges);q=len(edges);clauses=[];nv=0
def var():
 global nv
 nv+=1;return nv
def add(c):clauses.append(c)
def onehot(v):
 add(v)
 for a,b in it.combinations(v,2):add([-a,-b])
X=[[var() for j in range(q)] for e in edges]
for row in X:onehot(row)
for j in range(q):onehot([row[j] for row in X])
zero=var();add([-zero]);bits=[];w=q.bit_length()+2
for row in X:
 b=[var() for i in range(w)];bits.append(b)
 for j,x in enumerate(row):
  for i,z in enumerate(b):add([-x,z if (j+1)>>i&1 else -z])
def full(a,b,c):
 s=var();carry=var()
 for aa,bb,cc in it.product([0,1],repeat=3):
  pre=[-a if aa else a,-b if bb else b,-c if cc else c];t=aa+bb+cc
  add(pre+[s if t%2 else -s]);add(pre+[carry if t>=2 else -carry])
 return s,carry
def plus(a,b):
 carry=zero;out=[]
 for aa,bb in zip(a,b):s,carry=full(aa,bb,carry);out.append(s)
 add([-carry]);return out
for v in range(n*m):
 acc=[zero]*w
 for k,e in enumerate(edges):
  if v in e:acc=plus(acc,bits[k])
 target=4*n*m+2
 for i,z in enumerate(acc):add([z if target>>i&1 else -z])
# Every labeling can be transported to have the edge labelled 1 incident at vertex 0.
add([X[k][0] for k,e in enumerate(edges) if 0 in e])
tag=f'torus-{n}-{m}';(D/'outputs'/f'{tag}.cnf').write_text(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
(D/'outputs'/f'{tag}-model.json').write_text(json.dumps({'n':n,'m':m,'edges':edges,'X':X,'vars':nv,'clauses':len(clauses)},indent=2));print(nv,len(clauses))
