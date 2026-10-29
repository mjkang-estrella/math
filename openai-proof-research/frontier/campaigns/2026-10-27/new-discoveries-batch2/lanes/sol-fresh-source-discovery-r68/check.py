import math,json,pathlib,sys,functools
b=pathlib.Path(__file__).resolve().parent

def add(a,c):
 z=[0]*max(len(a),len(c))
 for i,x in enumerate(a):z[i]+=x
 for i,x in enumerate(c):z[i]+=x
 while len(z)>1 and z[-1]==0:z.pop()
 return z

def mul(a,c):
 z=[0]*(len(a)+len(c)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(c):z[i+j]+=x*y
 return z

def phi(n):return sum(math.gcd(i,n)==1 for i in range(1,n+1))
def compressed(n):
 ds=[d for d in range(2,n) if n%d==0]; w=[phi(n//d) for d in ds];t=len(ds)
 adj=[sum(1<<j for j,e in enumerate(ds) if j!=i and d*e%n==0) for i,d in enumerate(ds)]
 @functools.lru_cache(None)
 def rec(mask):
  if not mask:return (1,)
  i=max((i for i in range(t) if mask>>i&1),key=lambda i:(adj[i]&mask).bit_count()); rest=mask&~(1<<i)
  # Each gcd class is either a clique or an independent set.
  factor=[0,w[i]] if ds[i]**2%n==0 else [0]+[math.comb(w[i],k) for k in range(1,w[i]+1)]
  return tuple(add(rec(rest),mul(factor,rec(rest&~adj[i]))))
 return list(rec((1<<t)-1)),ds,w,rec.cache_info().currsize

def literal(n):
 vs=[x for x in range(1,n) if math.gcd(x,n)>1];m=len(vs)
 assert m<=24
 adj=[sum(1<<j for j,y in enumerate(vs) if i!=j and x*y%n==0) for i,x in enumerate(vs)]
 @functools.lru_cache(None)
 def f(mask):
  if not mask:return (1,)
  v=(mask&-mask).bit_length()-1;r=mask&~(1<<v)
  return tuple(add(f(r),[0]+list(f(r&~adj[v]))))
 return list(f((1<<m)-1))

def shape(a):
 downs=[i for i in range(len(a)-1) if a[i]>a[i+1]]
 valleys=[i for i in range(len(a)-1) if downs and i>downs[0] and a[i]<a[i+1]]
 lc=[i for i in range(1,len(a)-1) if a[i]*a[i]<a[i-1]*a[i+1]]
 return valleys,lc
if __name__=='__main__':
 lo,hi=map(int,sys.argv[1:3]);results=[];bad=[];nonlc=[];literalchecks=0
 for n in range(lo,hi+1):
  if n>1200 and sum(n%d==0 for d in range(2,math.isqrt(n)+1))>15:continue
  a,ds,w,states=compressed(n);v,lc=shape(a)
  if n<=40 and sum(w)<=24:assert a==literal(n);literalchecks+=1
  assert a[0]==1 and (len(a)==1 or a[1]==sum(w)) and all(x>=0 for x in a)
  if v:bad.append({'n':n,'valley_up_steps':v,'coefficients':a})
  if lc:nonlc.append({'n':n,'first':lc[0],'triple':a[lc[0]-1:lc[0]+2]})
  results.append({'n':n,'classes':len(ds),'states':states,'degree':len(a)-1,'mass':sum(a),'unimodal':not v,'log_concave':not lc})
 out={'range':[lo,hi],'cases':len(results),'literal_checks':literalchecks,'counterexamples':bad,'non_log_concave':nonlc,'results':results}
 (b/f'checks-{lo}-{hi}.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='results'})
