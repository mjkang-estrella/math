import pathlib,json,itertools,random,sys
D=pathlib.Path(__file__).resolve().parents[1]
def rank2(rows):
 piv={}
 for r in rows:
  while r:
   k=r.bit_length()
   if k not in piv:piv[k]=r;break
   r^=piv[k]
 return len(piv)
def invariants2(m,bits=12):
 n=len(m);a=[r[:] for r in m];k=0;e=0;out=[];mod=1<<bits
 while k<n and e<bits:
  pair=next(((i,j) for i in range(k,n) for j in range(k,n) if a[i][j]%2),None)
  if pair is None:
   if not any(a[i][j]%mod for i in range(k,n) for j in range(k,n)):out.extend([bits]*(n-k));break
   for i in range(k,n):
    for j in range(k,n):a[i][j]=(a[i][j]%mod)//2
   e+=1;mod//=2;continue
  i,j=pair;a[k],a[i]=a[i],a[k]
  for r in a:r[k],r[j]=r[j],r[k]
  inv=pow(a[k][k],-1,mod)
  for i in range(k+1,n):
   c=a[i][k]*inv%mod
   for j in range(k+1,n):a[i][j]=(a[i][j]-c*a[k][j])%mod
   a[i][k]=0
  out.append(e);k+=1
 return out
r=int(sys.argv[1]);N=1<<r;seen={};count=0;rng=random.Random(197)
for mask in range(1,1<<(N-1)) if r<=4 else (rng.getrandbits(N-1) for _ in range(20000)):
 S=[i+1 for i in range(N-1) if mask>>i&1];eig=tuple(sorted(2*sum((u&v).bit_count()%2 for v in S) for u in range(1,N)))
 if not eig or eig[0]==0:continue
 rows=[sum(1<<j for j in range(N) if ((i==j and len(S)%2) or (i!=j and (i^j) in S))) for i in range(N)]
 rk=rank2(rows)
 if eig in seen and seen[eig][1]!=rk:
  out={'r':r,'spectrum':eig,'S':S,'T':seen[eig][0],'rank_mod2':rk,'other_rank_mod2':seen[eig][1]};print(out,flush=True);(D/'outputs/sandpile-witness.json').write_text(json.dumps(out,indent=2));break
 # compare Smith 2-adic exponents only for first few cases for each spectral class
 if eig in seen and count%17==0:
  def lap(T):return [[len(T) if i==j else -int((i^j) in T) for j in range(1,N)] for i in range(1,N)]
  inv=invariants2(lap(S));old=invariants2(lap(seen[eig][0]))
  if inv!=old:
   out={'r':r,'spectrum':eig,'S':S,'T':seen[eig][0],'valuations':inv,'other_valuations':old};print(out,flush=True);(D/'outputs/sandpile-witness.json').write_text(json.dumps(out,indent=2));break
 else:seen[eig]=(S,rk)
 count+=1
else:print('NO WITNESS',flush=True)
print('connected generating subsets processed',count,'spectral classes',len(seen),flush=True)
