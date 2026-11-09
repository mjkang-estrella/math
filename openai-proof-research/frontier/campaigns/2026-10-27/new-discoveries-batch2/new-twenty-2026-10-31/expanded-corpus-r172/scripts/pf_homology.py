import pathlib,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1]
def partitions(n,lo=1):
 if not n:yield();return
 for a in range(lo,n+1):
  for q in partitions(n-a,a):yield(a,)+q
def rank(columns,p):
 basis={}
 for col in columns:
  c={i:a%p for i,a in col.items() if a%p}
  while c:
   v=max(c)
   if v not in basis:
    z=pow(c[v],-1,p);basis[v]={i:a*z%p for i,a in c.items()};break
   z=c[v]
   for i,a in basis[v].items():
    c[i]=(c.get(i,0)-z*a)%p
    if c[i]==0:del c[i]
 return len(basis)
start=time.monotonic();out=[];viol=[]
for n in range(2,11):
 for shape in partitions(n):
  if len(shape)<2:continue
  parts=[];offset=0
  for a in shape:parts.append(((1<<a)-1)<<offset);offset+=a
  for t in range(3,n+1):
   faces=[[] for _ in range(n+1)]
   for mask in range(1,1<<n):
    size=mask.bit_count();mx=max((mask&p).bit_count() for p in parts);longest=min(size,2*(size-mx)+1)
    if longest<t:faces[size].append(mask)
   ranks={p:[0]*(n+1) for p in (2,3)}
   for k in range(2,n+1):
    ix={m:i for i,m in enumerate(faces[k-1])};cols=[]
    for m in faces[k]:
     vs=[v for v in range(n) if m>>v&1];cols.append({ix[m^(1<<v)]:(-1)**j for j,v in enumerate(vs)})
    for p in (2,3):ranks[p][k]=rank(cols,p)
   betti={p:[len(faces[k])-ranks[p][k]-(ranks[p][k+1] if k<n else 0)-(1 if k==1 else 0) for k in range(1,n+1)] for p in (2,3)}
   rec={'parts':shape,'t_vertices':t,'reduced_betti_mod2':betti[2],'reduced_betti_mod3':betti[3]};out.append(rec)
   if betti[2]!=betti[3]:viol.append(rec)
   if time.monotonic()-start>105:break
  if time.monotonic()-start>105:break
 if time.monotonic()-start>105:break
r={'scope':'complete multipartite graphs by integer partitions of n2..10; every t3..n; exact boundary ranks over F2,F3; 105s internal cap','tested':len(out),'seconds':time.monotonic()-start,'torsion_diagnostics':viol,'records':out,'limitation':'Matching field Betti numbers does not prove integral torsion-free homology or wedge homotopy; t means vertices as in source, not edges.'}
(D/'outputs/pf-search.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k!='records'})
