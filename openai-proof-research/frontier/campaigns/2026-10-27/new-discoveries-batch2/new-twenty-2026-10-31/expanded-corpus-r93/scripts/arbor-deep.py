import itertools,functools,math,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def arbors(n):
 if n==0:return ()
 small=sorted((s,a) for s in range(1,n) for a in arbors(s))
 out=[]
 def forest(rem,start,children):
  if rem==0:yield tuple(children);return
  for j in range(start,len(small)):
   size,a=small[j]
   if size>rem:break
   yield from forest(rem-size,j,children+[a])
 for weight in range(1,n+1):
  for ch in forest(n-weight,0,[]):out.append((weight,ch))
 return tuple(out)
def size(a):return a[0]+sum(size(c) for c in a[1])
def lattice(a,t):
 weight,ch=a;n=size(a);arr=[math.comb(j+weight-1,weight-1) for j in range(t*n+1)]
 for c in ch:
  bb=lattice(c,t);arr=[sum(arr[j-i]*bb[i] for i in range(min(j,len(bb)-1)+1)) for j in range(len(arr))]
 return arr
out=[];n=int(sys.argv[1]);start=int(sys.argv[2]) if len(sys.argv)>2 else 0;stop=int(sys.argv[3]) if len(sys.argv)>3 else len(arbors(n))
for ix,a in enumerate(arbors(n)):
 if not start<=ix<stop:continue
 sets=[];counter=[0]
 def label(a):
  begin=counter[0];counter[0]+=a[0]
  for c in a[1]:label(c)
  sets.append(tuple(range(begin,counter[0])))
 label(a)
 L=[sum(lattice(a,t)) for t in range(n+1)]
 h=[sum((-1)**j*math.comb(n+1,j)*L[i-j] for j in range(i+1)) for i in range(n+1)]
 word=[0]*(n+1)
 for w in itertools.product(range(n),repeat=n):
  cs=[w.count(i) for i in range(n)]
  if all(sum(cs[i] for i in s)>=len(s) for s in sets):word[n-1-sum(w[i]>w[i+1] for i in range(n-1))]+=1
 if h!=word:print('WITNESS',ix,a,h,word,flush=True)
 print('tested',n,ix,flush=True);out.append({'index':ix,'arbor':a,'hstar':h,'word':word});(D/f'outputs/arbor-{n}-{start}-{stop}.json').write_text(json.dumps(out))
print('COMPLETE',n,start,stop,'total_arbors',len(arbors(n)),flush=True)
