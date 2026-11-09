import pathlib,itertools,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
def canon(r):
 n=len(r);out=[]
 for t in [r,r[::-1]]:
  for j in range(n):
   a=t[j:]+t[:j];m={};b=[]
   for c in a:
    if c not in m:m[c]=len(m)
    b.append(m[c])
   out.append(tuple(b))
 return min(out)
def polynomial(r):
 n=len(r);p=[0]*(n+1)
 for mask in range(1<<n):
  par=list(range(n))
  def root(i):
   while par[i]!=i:i=par[i]
   return i
  for i in range(n):
   if mask>>i&1:par[root(i)]=root((i+1)%n)
  comps={}
  for i in range(n):comps.setdefault(root(i),set()).add(r[i])
  a=[(-1)**mask.bit_count()]
  for s in comps.values():
   b=[0]*(len(a)+1)
   for k,v in enumerate(a):b[k]-=len(s)*v;b[k+1]+=v
   a=b
  for k,v in enumerate(a):p[k]+=v
 return p
out=[]
for n in range(5,int(sys.argv[1])+1,2):
 candidates=set();raw=0
 # exactly three nonconstant transitions along the step-two n-cycle
 for a in range(1,n-1):
  for b in range(1,n-a):
   seq=[0]*a+[1]*b+[2]*(n-a-b);r=[0]*n
   for k,v in enumerate(seq):r[2*k%n]=v
   if any(r[i]==r[(i+1)%n] for i in range(n)):continue
   raw+=1;candidates.add(canon(r))
 vals=[(tuple(reversed(polynomial(r))),r) for r in candidates];best=max(vals)[0];w=[r for p,r in vals if p==best]
 row={'n':n,'proper_three_run_compositions':raw,'dihedral_colour_orbits':len(candidates),'maximizers':w,'polynomial_descending':best};out.append(row);print(row,flush=True)
 (D/'outputs/restraints.json').write_text(json.dumps(out,indent=2)+'\n')
