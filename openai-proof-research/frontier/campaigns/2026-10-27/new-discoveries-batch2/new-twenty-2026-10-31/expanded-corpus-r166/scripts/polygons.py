import math,json,pathlib,time
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def calc(k,n,eps):
 R=1/(2*math.sin(math.pi/n)); polys=[]
 for j in range(k):
  a=2*math.pi*j/k; shift=(eps*R*math.cos(a),eps*R*math.sin(a))
  polys.append([(R*math.cos(a+2*math.pi*t/n)+shift[0],R*math.sin(a+2*math.pi*t/n)+shift[1]) for t in range(n)])
 P=A=0
 for i,p in enumerate(polys):
  for t,a in enumerate(p):
   b=p[(t+1)%n];d=sub(b,a);intervals=[]
   for j,q in enumerate(polys):
    if i==j:continue
    lo,hi=0.,1.
    for s,u in enumerate(q):
     v=q[(s+1)%n];e=sub(v,u);v0=cross(e,sub(a,u));vd=cross(e,d)
     if abs(vd)<1e-14:
      if v0<0:hi=-1;break
     elif vd>0:lo=max(lo,-v0/vd)
     else:hi=min(hi,-v0/vd)
     if lo>=hi:break
    if hi>lo:intervals.append((lo,hi))
   prev=0;visible=0
   for lo,hi in sorted(intervals):
    if lo>prev:visible+=lo-prev
    prev=max(prev,hi)
   visible+=1-prev;P+=math.hypot(*d)*visible;A+=cross(a,b)*visible/2
 return P,A,P/A-4*math.tan(math.pi/n)
rows=[];start=time.monotonic()
for n in range(3,14):
 for k in range(2,42):
  if math.gcd(n,k)>1:continue
  # Small shifts chosen below the local boundary combinatorics scale.
  eps=1e-3/(k*n)
  P,A,d=calc(k,n,eps);expected=k%n==1
  row={'k':k,'n':n,'relative_radius_shift':eps,'perimeter':P,'area':A,'ratio_difference':d,'difference_over_eps2':d/eps**2,'expected_positive':expected,'numerical_sign_matches':(d>0)==expected if abs(d)>1e-12 else None};rows.append(row)
  if row['numerical_sign_matches']==False:print('MISMATCH',row,flush=True)
 print('n',n,'rows',len(rows),'seconds',time.monotonic()-start,flush=True)
(D/'outputs/polygon-sweep.json').write_text(json.dumps(rows,indent=2));print('complete',len(rows))
