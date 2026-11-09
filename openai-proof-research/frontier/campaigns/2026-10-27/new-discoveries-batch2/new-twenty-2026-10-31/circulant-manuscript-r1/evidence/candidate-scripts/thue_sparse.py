import functools,math,random,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
import sys
sys.setrecursionlimit(10000)
terms={j:[(i+h,j-i+h,math.comb(j,i)*math.comb(6-j,h)) for i in range(j+1) for h in range(7-j)] for j in range(7)}
@functools.lru_cache(None)
def R(j,n):
 if n<0:return 0
 if n==0:return int(j==6)
 return sum(c*R(k,(n-s)//2) for s,k,c in terms[j] if n>=s and (n-s)%2==0)
rng=random.Random(108);out=[]
for power in [10,20,50,100,200,500]:
 points=sorted({(1<<power)+d for d in range(-50,51)}|{(1<<power)-1,(1<<(power+1))-1}|{rng.randrange(1<<power,1<<(power+1)) for _ in range(100)})
 bad=[]
 for n in points:
  for j in [0,6]:
   d=R(j,n+1)-R(j,n)
   if d<=0:bad.append([j,str(n),str(d)])
 out.append(dict(binary_power=power,points=[str(n) for n in points],nonpositive=bad));print(power,len(points),len(bad),R.cache_info(),flush=True);R.cache_clear()
(D/'outputs/thue-sparse.json').write_text(json.dumps(out,indent=2))
