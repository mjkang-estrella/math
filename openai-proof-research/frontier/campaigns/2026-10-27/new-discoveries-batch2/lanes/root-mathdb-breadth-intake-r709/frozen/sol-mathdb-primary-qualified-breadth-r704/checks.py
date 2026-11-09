import pathlib,json,itertools,time
P=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
sieve=bytearray(b'\1')*20001;sieve[:2]=b'\0\0'
for p in range(2,142):
 if sieve[p]:sieve[p*p::p]=b'\0'*len(sieve[p*p::p])
hits=[];steps=0
for p in range(2,20001):
 if not sieve[p]:continue
 v=1;m=p*p
 for n in range(1,min(2000,p-1)+1):
  v=v*n%m;steps+=1
  if v==m-1:hits.append({'n':n,'p':p,'square':m})
# Enumerate the exact primary definition: pi and pi^2 both avoid both patterns.
def avoid(a):
 n=len(a)
 if any(a[i]>a[j]>a[k] for i,j,k in itertools.combinations(range(n),3)):return False
 return not any(a[i]<a[l]<a[j]<a[k] for i,j,k,l in itertools.combinations(range(n),4))
f=[0,1]
for n in range(10):f.append(sum(f[-2:]))
counts=[]
for n in range(1,9):
 count=sum(1 for p in itertools.permutations(range(n)) if avoid(p) and avoid(tuple(p[p[i]] for i in range(n))))
 counts.append({'n':n,'count':count,'conjectured':2*f[n+2]-n-2})
o={'executed':True,'factorial':{'n_range':[1,2000],'prime_range':[2,20000],'modular_multiplications':steps,'hits':hits,'new_exception_hits':[x for x in hits if x['n'] not in {4,5,7,12,23,229,562}],'limit':'No exclusion of larger prime-square divisors; no all-n result.'},'strong_avoidance':{'exhaustive_n':[1,8],'counts':counts,'limit':'Only finite sanity test; no full-scope recurrence or theorem.'},'wall_seconds':time.monotonic()-t}
(P/'bounded-calculations.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
