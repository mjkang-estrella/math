from pathlib import Path
import sys,time,json,math,argparse
sys.path.insert(0,str(Path(__file__).parent/'.pydeps'))
from flint import fmpz_poly
x=fmpz_poly([0,1]); one=fmpz_poly([1])

def binomial_polynomial(k):return x**k+1

def binary_search(N):
 A=[one,one]; found=[]; start=time.monotonic()
 for n in range(2,N+1):
  if n%2:A.append(A[-1]);continue
  f=one; v=(n & -n).bit_length()-1
  for i in range(1,v+1):f*=binomial_polynomial(2**i)
  a=((x+1)**n)*A[n//2].inflate(2)+f*A[n-2]
  A.append(a)
  c=list(map(int,a.coeffs()));half=len(c)//2
  for j in range(half):
   if c[j]>c[j+1]:found.append({'kind':'binary-unimodality','n':n,'j':j,'values':c[j:j+2]});break
  for j in range(1,half+1):
   if c[j]*c[j]<c[j-1]*c[j+1]:found.append({'kind':'binary-logconcavity','n':n,'j':j,'values':c[j-1:j+2]});break
  for d in [2**i for i in range(n.bit_length())]:
   if not (a%binomial_polynomial(d)):found.append({'kind':'binary-divisibility','n':n,'power':d})
  if any(f['n']==n for f in found):
   print(json.dumps({'found_at':n,'events':[f for f in found if f['n']==n]}),flush=True)
  if n%50==0:print(json.dumps({'binary_checked':n,'degree':a.degree(),'seconds':round(time.monotonic()-start,2)}),flush=True)
 return found

def denominator(n):
 d=one
 for i in range(1,n+1):d*=binomial_polynomial(i)**((n//i).bit_length())
 return d

def ordinary(n):
 d=denominator(n); a=[fmpz_poly([0]) for _ in range(n+1)];a[0]=d
 for i in range(1,n+1):
  f=binomial_polynomial(i)
  for s in range(i,n+1):
   q,r=divmod(a[s-i],f)
   if r:raise RuntimeError(('inexact',n,i,s))
   a[s]+=q
 return a[n],d

def ordinary_search(N,factor=False):
 found=[];start=time.monotonic()
 for n in range(2,N+1):
  a,d=ordinary(n);c=list(map(int,a.coeffs()))
  # Intended even-part reading: compress the even coefficient subsequence;
  # inserted zero odd coefficients would be a trivial wording failure.
  even=c[::2];half=len(even)//2
  for j in range(half):
   if even[j]>even[j+1]:found.append({'kind':'ordinary-even-unimodality','n':n,'j':j,'values':even[j:j+2]});break
  g=a.gcd(d)
  if g.degree()>0:found.append({'kind':'ordinary-gcd','n':n,'factor':str(g)})
  if factor:
   content,fac=a.factor()
   if n>=3 and (len(fac)>1 or any(e>1 for _,e in fac)):
    found.append({'kind':'ordinary-irreducibility','n':n,'content':str(content),'factors':[(str(p),e) for p,e in fac]})
  if found:
   print(json.dumps({'found':found}),flush=True);break
  print(json.dumps({'ordinary_checked':n,'degree':a.degree(),'seconds':round(time.monotonic()-start,2)}),flush=True)
 return found

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['binary','ordinary']);p.add_argument('N',type=int);p.add_argument('--factor',action='store_true');args=p.parse_args()
 r=binary_search(args.N) if args.mode=='binary' else ordinary_search(args.N,args.factor)
 Path(__file__).with_name('search-'+args.mode+'-result.json').write_text(json.dumps({'N':args.N,'factor':args.factor,'found':r},indent=2)+'\n')
