import pathlib,sys,itertools,json
L=pathlib.Path(__file__).resolve().parents[1];m,n=map(int,sys.argv[1:]);v=m*n;N=3*v
cs=[];nv=0;vs={}
def var(a,b):
 global nv
 if a>b:return -var(b,a)
 if (a,b) not in vs:nv+=1;vs[a,b]=nv
 return vs[a,b]
def less(a,b):return var(a,b)
for a,b,c in itertools.combinations(range(N),3):
 cs.extend([[-less(a,b),-less(b,c),less(a,c)],[less(a,b),less(b,c),-less(a,c)]])
for a in range(v):
 cs.extend([[less(3*a,3*a+1)],[less(3*a+1,3*a+2)]])
for x in range(1,N):cs.append([less(0,x)])
for a,b in itertools.combinations(range(v),2):
 xa,ya=divmod(a,n);xb,yb=divmod(b,n)
 edge=(xa==xb and (ya-yb)%n in [1,n-1]) or (ya==yb and (xa-xb)%m in [1,m-1])
 chains=[]
 for x,y in [(a,b),(b,a)]:
  seq=[3*x,3*y,3*x+1,3*y+1,3*x+2,3*y+2]
  chains.append([less(i,j) for i,j in zip(seq,seq[1:])])
 if edge:
  nv+=1;o=nv
  cs.extend([[-o,z] for z in chains[0]]);cs.extend([[o,z] for z in chains[1]])
 else:cs.extend([[-z for z in chain] for chain in chains])
p=L/'work'/f'grid-{m}-{n}.cnf'
with p.open('w') as f:
 f.write(f'p cnf {nv} {len(cs)}\n')
 for c in cs:f.write(' '.join(map(str,c))+' 0\n')
(L/'work'/f'grid-{m}-{n}.vars.json').write_text(json.dumps([[a,b,i] for (a,b),i in vs.items()]))
print(p,nv,len(cs))
