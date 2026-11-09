import itertools,json,pathlib,time,math
D=pathlib.Path(__file__).resolve().parents[1];mode=__import__('sys').argv[1];out=[]
if mode=='divine':
 for N in [32,64,128,256,512]:
  divs=[[] for _ in range(N+1)]
  for d in range(1,N+1):
   for k in range(2*d,N+1,d):divs[k].append(d)
  f=[0]*(N+1);f[1]=1;S=[0]*(N+1);S[1]=1;nodes=[0];best=[1];start=time.monotonic()
  def dfs(n):
   nodes[0]+=1;best[0]=max(best[0],n-1)
   if n>N:return True
   if nodes[0]>1000000 or time.monotonic()-start>18:return False
   opts=[-f[n//2]] if n%2==0 else [-1,1]
   for s in opts:
    if any(f[d]*(S[d]+s)>1 for d in divs[n]):continue
    f[n]=s;S[n]=s
    for d in divs[n]:S[d]+=s
    if dfs(n+1):return True
    for d in divs[n]:S[d]-=s
   f[n]=0;S[n]=0;return False
  found=dfs(2);checks=all(sum(f[d*j]*f[d] for j in range(2,k+1))<=0 for d in range(1,N+1) for k in range(2,N//d+1)) if found else None
  r={'N':N,'found':found,'nodes':nodes[0],'deepest':best[0],'verified_every_cascade':checks,'colors':f[1:] if found else None};out.append(r);print({k:v for k,v in r.items() if k!='colors'},flush=True)
if mode=='tiles':
 for n,k,w in [(7,3,14),(7,3,21),(7,3,28),(7,3,35),(8,3,16),(8,3,24),(9,4,18),(9,4,27)]:
  prefix=list(range(n-k));cases=tiles=0;bad=[];full=(1<<w)-1;start=time.monotonic()
  for extra in itertools.combinations(range(n-k,w),k):
   A=prefix+list(extra)
   if sorted(a%n for a in A)==list(range(n)):continue
   cases+=1;rots=[sum(1<<((a+b)%w) for a in A) for b in range(w)]
   def rec(mask,chosen):
    if mask==full:return chosen
    bit=((~mask)&full)&-((~mask)&full);v=bit.bit_length()-1
    for a in A:
     b=(v-a)%w;r=rots[b]
     if not r&mask:
      z=rec(mask|r,chosen+[b])
      if z is not None:return z
    return None
   z=rec(rots[0],[0])
   if z is not None:tiles+=1;bad.append({'A':A,'B':z})
  r={'n':n,'k':k,'omega':w,'nonstandard_A_tested':cases,'tilings':tiles,'witnesses':bad,'seconds':time.monotonic()-start};out.append(r);print(r,flush=True)
(D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
