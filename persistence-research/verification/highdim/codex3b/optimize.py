"""Generator-only arithmetic caches; independent certificate replay is unchanged."""
import math
import gen_hd
class FastGen(gen_hd.Gen):
 def __init__(self,*args,**kwargs):
  super().__init__(*args,**kwargs)
  self.norm_cache={};self.answer_cache={}
 def aligned(self,M):
  o=super().aligned(M)
  # A full <3,7> subgroup still kills T=0. The prior search dropped these primes.
  # Keep small such primes, whose zero test is cheap and often useful.
  if not o.get('_full_added'):
   full=[e for e in o['ee'] if e[4]==e[0]-1 and e[0]<=10000]
   o['uu']=o['uu']+full;o['_full_added']=True
  return o
 def expand(self,r,M,f):
  import itertools
  from hnt import vp
  self.current={"r":list(r),"M":M,"factor":f}
  M2=M*f;used=[];alive=[]
  a0,w0=self.sig(r,M)
  same_a=f%3!=0;same_w=M%6==0 and f%7!=0
  if not same_a:j=vp(M2,3);m3=3**(j+2);per3=3**j
  if not same_w and M2%6==0:i=vp(M2,7);m7=7**(i+1);per7=6*7**i
  for t in itertools.product(range(f),repeat=self.dim):
   r2=tuple(x+k*M for x,k in zip(r,t))
   if same_a:a=a0
   else:
    x=self.xm(r2,m3,per3);v=vp(x,3) if x else j+2;a=(v,v) if x else (v,None)
   if same_w:w=w0
   elif M2%6:w=(0,None)
   else:
    x=self.xm(r2,m7,per7);v=vp(x,7) if x else i+1;w=(v,v) if x else (v,None)
   e=self.kill(r2,M2,a,w,used)
   if e is None:alive.append((r2,a,w))
   elif e not in used:used.append(e)
  return alive,used
 def test(self,e,r,a,w):
  p,d,o3,o7,H,pw,cw,i2=e
  if pw is None:
   T=(pow(10,r[0]%d,p)+self.K+sum(c*pow(10,x%d,p) for c,x in zip(self.coefs,r[1:]))) * i2%p
  else:
   T=(pw[r[0]%d]+self.K+sum(cw[i][r[i+1]%d] for i in range(self.dim-1))) * i2%p
  if not T:return True
  af,wf=a[1] is None,w[1] is None
  order=H if af and wf else o3 if af else o7 if wf else 1
  if order==p-1:return False
  nk=(p,a[0],w[0]);norm=self.norm_cache.get(nk)
  if norm is None:
   norm=pow(3,-a[0],p)*pow(7,-w[0],p)%p;self.norm_cache[nk]=norm
  x=T*norm%p
  if order==1:return x!=1
  if p<10000:
   ck=(p,order,x);ans=self.answer_cache.get(ck)
   if ans is None:
    ans=pow(x,order,p)!=1;self.answer_cache[ck]=ans
   return ans
  return pow(x,order,p)!=1
