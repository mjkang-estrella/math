from pathlib import Path
import sys,json,collections,math
D=Path(__file__).resolve().parents[1]
def poly(n):
 nums=list(range(2,6*n+1,2));dens=list(range(2,2*n+2))+list(range(4,2*n+3,2));deg=sum(nums)-sum(dens)
 # Formal power series division exact through the claimed total degree, with tail check.
 cap=deg+max(nums+dens)+1;a=[0]*(cap+1);a[0]=1
 for k in nums:
  for j in range(cap,k-1,-1):a[j]-=a[j-k]
 for k in dens:
  for j in range(k,cap+1):a[j]+=a[j-k]
 assert not any(a[deg+1:]),(n,'non-polynomial tail')
 assert min(a[:deg+1])>=0,(n,'negative')
 return a[:deg+1]
def generate(n,a=0,b=0,c=0,w=b''):
 if a+b+c==3*n:yield w;return
 if a<n:yield from generate(n,a+1,b,c,w+b'\0')
 if b<a:yield from generate(n,a,b+1,c,w+b'\1')
 if c<a:yield from generate(n,a,b,c+1,w+b'\2')
def promote(w):
 cnt=[0,0,0];els=[]
 for x in w:els.append((x,cnt[x]));cnt[x]+=1
 for i in range(len(els)-1):
  (x,j),(y,k)=els[i:i+2]
  # In the current linear extension x<y iff same chain, or x=A and j<=k.
  comparable=x==y or (x==0 and j<=k) or (y==0 and k<=j)
  if not comparable:els[i],els[i+1]=els[i+1],els[i]
 return bytes(x for x,j in els)
mode=sys.argv[1]
if mode=='poly':
 rows=[]
 for n in range(1,41):
  a=poly(n);rows.append({'n':n,'degree':len(a)-1,'coefficient_sum':sum(a),'minimum':min(a)})
 (D/'outputs/promotion-polynomials.json').write_text(json.dumps(rows,indent=2)+'\n');print(rows[-1])
else:
 n=int(mode);seen=set();hist=collections.Counter();total=0
 for w in generate(n):
  total+=1
  if w in seen:continue
  v=w;k=0
  while v not in seen:
   seen.add(v);v=promote(v);k+=1
  assert v==w;assert 6*n%k==0
  hist[k]+=1
 a=poly(n);L=6*n;res=[0]*L
 for j,c in enumerate(a):res[j%L]+=c
 expected=[0]*L
 for size,count in hist.items():
  for j in range(size):expected[j*L//size]+=count
 r={'n':n,'linear_extensions':total,'orbits':dict(hist),'csp_residue_equal':res==expected,'group_order_used':L,'actual_order':math.lcm(*hist),'residues':res,'expected':expected}
 (D/f'outputs/promotion-{n}.json').write_text(json.dumps(r,indent=2)+'\n');print(r);assert res==expected
