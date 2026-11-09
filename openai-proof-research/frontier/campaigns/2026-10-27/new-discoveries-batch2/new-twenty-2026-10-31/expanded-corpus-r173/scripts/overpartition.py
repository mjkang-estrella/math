import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];N=255
# Literal product over odd part sizes ((1+q^s)/(1-q^s))^k, modular truncated arithmetic.
def mul(a,b,mod):
 c=[0]*(N+1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b[:N+1-i]):
    if y:c[i+j]=(c[i+j]+x*y)%mod
 return c
def powr(a,k,mod):
 b=[1]+[0]*N
 while k:
  if k&1:b=mul(b,a,mod)
  k//=2
  if k:a=mul(a,a,mod)
 return b
mod=2**20;base=[1]+[0]*N
for s in range(1,N+1,2):
 # multiply by 1+2q^s+2q^(2s)+... using unbounded coin recurrence
 for j in range(s,N+1):base[j]=(base[j]+base[j-s])%mod
 prev=base.copy()
 for j in range(s,N+1):base[j]=(base[j]+prev[j-s])%mod
rows=[]
for i in range(1,7):
 for r in [1,3,5,7]:
  a=powr(base,(2**i)*r,mod);bad=[];tests=0
  for residue,e in [(2,2*i+1),(4,2*i+4),(6,2*i+3),(7,i+4)]:
   for n in range(residue,N+1,8):
    tests+=1
    if a[n]%(2**e):bad.append([n,e,a[n]])
  rows.append({'i':i,'r':r,'tests':tests,'failures':bad});print(rows[-1],flush=True)
(D/'outputs/overpartition.json').write_text(json.dumps({'max_coefficient':N,'rows':rows,'modulus':mod},indent=2))
