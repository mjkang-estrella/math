import os,resource,pathlib,json,itertools,cmath,math
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1];out=[]
def roots(c):
 n=len(c)-1;c=[v/c[-1] for v in c];radius=1+max(abs(x) for x in c[:-1]);zs=[radius*cmath.exp(2j*math.pi*(k+.17)/n) for k in range(n)]
 def f(z):
  a=0j
  for v in reversed(c):a=a*z+v
  return a
 for _ in range(500):
  changes=[]
  for j,z in enumerate(zs):
   den=1j*0+1
   for k,w in enumerate(zs):
    if j!=k:den*=z-w
   changes.append(f(z)/den if abs(den)>1e-100 else 0)
  zs=[z-v for z,v in zip(zs,changes)]
  if max(map(abs,changes))<1e-11:break
 return zs,max(abs(f(z)) for z in zs)
for d in range(2,7):
 basis=[]
 for j in range(d+1):
  c=[1]
  for r in range(d):
   b=d-j-r;c=[b*c[0]]+[c[i-1]+b*c[i] for i in range(1,len(c))]+[c[-1]]
  basis.append(c)
 lo=0.;hi=d*d
 for _ in range(90):
  mid=(lo+hi)/2;phi=sum(2*math.atan((j+.5)/mid) for j in range(d))
  if phi>math.pi:lo=mid
  else:hi=mid
 bound=hi;count=0;bad=[];unstable=0;largest=0
 for h in itertools.product(range(3),repeat=d+1):
  if not any(h):continue
  c=[sum(h[j]*basis[j][r] for j in range(d+1)) for r in range(d+1)];zs,res=roots(c);count+=1
  if res>1e-5:unstable+=1;continue
  maxy=max(abs(z.imag) for z in zs);largest=max(largest,maxy)
  if maxy>bound+1e-7:bad.append({'h':h,'roots':[(z.real,z.imag) for z in zs],'residual':res})
 row={'id':380100,'d':d,'all_coefficients_h_in':[0,1,2],'nonzero_vectors':count,'numerically_unstable':unstable,'Md_bound':bound,'largest_observed':largest,'counterexamples':bad,'limitation':'floating point Durand-Kerner roots, not certified; only finite coefficient cube'};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/snn-search.json').write_text(json.dumps(out,indent=2))
