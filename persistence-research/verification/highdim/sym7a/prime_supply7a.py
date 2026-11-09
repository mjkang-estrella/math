"""Search-only supply: primes p with 2,3,5,7-smooth p-1 and decimal order."""
import sys
sys.dont_write_bytecode=True
import collections,hashlib,json,math,pathlib,time
H=pathlib.Path(__file__).resolve().parent

def prime(n):
 if n<2:return False
 for p in (2,3,5,7,11,13,17,19,23,29,31,37):
  if n%p==0:return n==p
 d=n-1;s=0
 while d%2==0:d//=2;s+=1
 for a in (2,325,9375,28178,450775,9780504,1795265022):
  if a%n==0:continue
  x=pow(a,d,n)
  if x in (1,n-1):continue
  for _ in range(s-1):
   x=x*x%n
   if x==n-1:break
  else:return False
 return True

def order(a,p):
 n=p-1
 for f in (2,3,5,7):
  while n%f==0 and pow(a,n//f,p)==1:n//=f
 return n

def main():
 start=time.monotonic();old=json.loads((H/'supply.json').read_text());known={x[0] for x in old};added=[];tried=0
 for a in range(1,23):
  for b in range(11):
   for c in range(1,10):
    for d in range(7):
     p=1+2**a*3**b*5**c*7**d
     if p>10**10 or p in known:continue
     tried+=1
     if not prime(p):continue
     r=[p,order(10,p),order(3,p),order(7,p)]
     if r[1]<=3000000:
      added.append(r);known.add(p)
 added=sorted(added,key=lambda r:(r[1],-(r[0]-1)/math.lcm(r[2],r[3]),r[0]))[:128]
 data=sorted(old+added)
 # A supply hint never discharges a proof obligation; original checkers recompute.
 (H/'supply.json').write_text(json.dumps(data,indent=1)+'\n')
 (H/'prime_supply_audit.json').write_text(json.dumps({'label':'COMPUTED','tried':tried,'old_count':len(old),'added_count':len(added),'seconds':time.monotonic()-start,'added':added,'screen':'deterministic Miller-Rabin below 2^64; exact order reduction using known p-1 factors 2,3,5,7','selection':'p<=1e10; 5 divides p-1; ord10<=3e6','note':'Untrusted search optimization; witnesses require both original CLI checks'},indent=1)+'\n')
 print('added',len(added),'seconds',round(time.monotonic()-start,2))
if __name__=='__main__':main()
