import pathlib,json,math,sys,itertools
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def emit(x):
 out.append(x);print(x,flush=True);(D/'outputs'/f'{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
if mode=='dickson':
 for p in [x for x in range(3,152,2) if all(x%d for d in range(2,math.isqrt(x)+1))]:
  a=[2]*p;b=[1]*p;cpp=[]
  for n in range(1,p*p):
   if len(set(b))==p and len({(v+x)%p for x,v in enumerate(b)})==p:cpp.append(n)
   a,b=b,[(b[x]-x*a[x])%p for x in range(p)]
  pred=sorted({2,2*p,3,3*p}|({p+1,p+2,2*p+1} if p%12==1 else set()))
  emit({'p':p,'n_range':[1,p*p-1],'actual':cpp,'predicted':pred,'match':cpp==pred})
 p=5;a=[1]*p;b=[1]*p;good=[];states=[]
 for n in range(1,1201):
  if len(set(b))==5:good.append(n)
  if n in [1,121]:states.append([n,a,b])
  a,b=b,[(b[x]-x*a[x])%p for x in range(p)]
 emit({'second_kind_n_range':[1,1200],'good':good,'match':all((n in good)==(n%120 in [2,3,15,94]) for n in range(1,1201)),'states':states})
if mode=='digits':
 import numpy as np
 from scipy.optimize import linprog
 for p in [x for x in range(13,402,4) if all(x%d for d in range(2,math.isqrt(x)+1))]:
  ds=list(range((p+1)//2))+[(p+3)//2];dset=set(ds);ix={v:j for j,v in enumerate(ds)}
  aps=[[(a+i*b)%p for i in range(4)] for a in ds for b in range(1,p) if all((a+i*b)%p in dset for i in range(4))]
  A=np.zeros((3*len(ds),len(aps)))
  for j,ap in enumerate(aps):
   for k in range(1,4):A[(k-1)*len(ds)+ix[ap[k]],j]+=1;A[(k-1)*len(ds)+ix[ap[0]],j]-=1
  res=linprog(np.zeros(len(aps)),A_eq=np.vstack([A,np.ones(len(aps))]),b_eq=np.r_[np.zeros(A.shape[0]),1],bounds=(0,None),method='highs')
  emit({'p':p,'digits':ds,'nonconstant_coordinate_APs':len(aps),'LP_status':res.status,'message':res.message,'support':None if not res.success else [(aps[j],float(x)) for j,x in enumerate(res.x) if x>1e-8]})
if mode=='squares':
 N=3000001;sq={i*i for i in range(math.isqrt(N)+1)};two=bytearray(N+1)
 for a in range(math.isqrt(N)+1):
  for b in range(a,math.isqrt(N-a*a)+1):two[a*a+b*b]=1
 def iota(n):
  if n in sq:return 1
  if two[n]:return 2
  while n%4==0:n//=4
  return 4 if n%8==7 else 3
 maxtrials=0;bad=[];hist={}
 for a in range(31,1000001):
  trials=0
  for r in range(a-1,0,-1):
   if iota(r)!=4:continue
   trials+=1
   if iota(a+r)>=3 and iota(2*a+r)>=2:break
  else:bad.append(a)
  maxtrials=max(maxtrials,trials);hist[trials]=hist.get(trials,0)+1
 emit({'a_range':[31,1000000],'bad':bad,'max_four_square_candidates_needed':maxtrials,'hist':hist,'method':'exact square/two-square enumeration and Legendre criterion; tests existence required by source Theorem 2.8, not direct semigroup oracle'})
