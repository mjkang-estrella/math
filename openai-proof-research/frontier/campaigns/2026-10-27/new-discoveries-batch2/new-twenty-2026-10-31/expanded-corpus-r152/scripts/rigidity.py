import itertools,random,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];P=1000003;rng=random.Random(152)
def rank(rows):
 basis={}
 for row in rows:
  a=[v%P for v in row]
  for j in sorted(basis):
   if a[j]:
    z=a[j];a=[(v-z*w)%P for v,w in zip(a,basis[j])]
  j=next((j for j,v in enumerate(a) if v),None)
  if j is not None:
   inv=pow(a[j],-1,P);basis[j]=[v*inv%P for v in a]
 return len(basis)
def case(n,faces):
 p=[[rng.randrange(P) for _ in range(3)] for _ in range(n)];edges=list(itertools.combinations(range(n),2));ei={e:i for i,e in enumerate(edges)};R=[];B=[];fm=[]
 for a,b in edges:
  row=[0]*(3*n)
  for j in range(3):row[3*a+j]=p[a][j]-p[b][j];row[3*b+j]=-row[3*a+j]
  R.append(row)
 for a,b,c in faces:
  u=[p[b][j]-p[a][j] for j in range(3)];v=[p[c][j]-p[a][j] for j in range(3)];uu=sum(x*x for x in u);vv=sum(x*x for x in v);uv=sum(x*y for x,y in zip(u,v));row=[0]*(3*n)
  for j in range(3):row[3*b+j]=vv*u[j]-uv*v[j];row[3*c+j]=uu*v[j]-uv*u[j];row[3*a+j]=-row[3*b+j]-row[3*c+j]
  B.append(row);fm.append(sum(1<<ei[e] for e in itertools.combinations((a,b,c),2)))
 m=len(faces);cache={0:0};union=[0]*(1<<m); rr=[0]*(1<<m);br=[0]*(1<<m)
 for mask in range(1,1<<m):
  bit=mask&-mask;j=bit.bit_length()-1;es=union[mask^bit]|fm[j];union[mask]=es
  if es not in cache:cache[es]=rank([row for k,row in enumerate(R) if es>>k&1])
  rr[mask]=cache[es];br[mask]=rank([row for k,row in enumerate(B) if mask>>k&1])
 bad=[];tests=range(1<<m) if n==5 else [(1<<m)-1]
 for mask in tests:
  target=mask.bit_count();sub=mask
  while sub:
   target=min(target,rr[sub]+(mask^sub).bit_count());sub=(sub-1)&mask
  if br[mask]!=target:bad.append(dict(mask=mask,volume_rank=br[mask],rado_rank=target))
 return dict(n=n,faces=faces,tests=len(tests),discrepancies=bad,prime=P)
out=[case(5,list(itertools.combinations(range(5),3)))];print(json.dumps(out[-1]),flush=True)
for n in range(6,10):
 for _ in range(4):
  faces=rng.sample(list(itertools.combinations(range(n),3)),10);r=case(n,faces);out.append(r);print(json.dumps(r),flush=True)
 (L/'outputs/rigidity.json').write_text(json.dumps(out,indent=2))
