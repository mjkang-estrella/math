import itertools,json
from pathlib import Path

def count(w,h):
 rows=[r for r in itertools.product(range(3),repeat=w) if all(a!=b for a,b in zip(r,r[1:]))]
 compat=[[j for j,s in enumerate(rows) if all(a!=b for a,b in zip(r,s))] for r in rows]
 v=[1]*len(rows)
 for _ in range(h-1):v=[sum(v[j] for j in js) for js in compat]
 return sum(v)
# Independent vertex-by-vertex backtracking at width 4, normalized first edge.
def brute(w,h):
 a=[-1]*(w*h);total=0
 def go(i):
  nonlocal total
  if i==len(a):total+=1;return
  for c in range(3):
   if i==0 and c!=0:continue
   if i==1 and c!=1:continue
   if i%w and a[i-1]==c:continue
   if i>=w and a[i-w]==c:continue
   a[i]=c;go(i+1)
 go(0);return total
r={f'{w}x{h}':count(w,h) for w,h in [(4,4),(4,7),(7,7),(3,3),(3,7),(5,5)]}
b=brute(4,4)
assert b*6==r['4x4']
assert all(r[k]%6==0 for k in r)
assert r['7x7']%12==r['4x7']%12==r['4x4']%12==0
# Exact color-orbit representatives verify folding on smaller sizes.
def reps(w,h):
 a=[-1]*(w*h);out=set()
 def go(i):
  if i==len(a):out.add(tuple(a));return
  for c in range(3):
   if i==0 and c!=0:continue
   if i==1 and c!=1:continue
   if i%w and a[i-1]==c:continue
   if i>=w and a[i-w]==c:continue
   a[i]=c;go(i+1)
 go(0);return out

def canon(a):
 d={};return tuple(d.setdefault(c,len(d)) for c in a)
fold=[]
for w,h in [(3,3),(3,4),(5,2),(5,3)]:
 rr=reps(w,h);fix=0
 for a in rr:
  reflected=tuple(a[y*w+w-1-x] for y in range(h) for x in range(w))
  fix+=canon(reflected)==a
 target=count((w+1)//2,h)//6
 assert fix==target and len(rr)%2==target%2
 fold.append([w,h,len(rr),fix,target])
print(json.dumps({'color_counts':r,'normalized_4x4_backtrack':b,'fold_checks':fold,'assertions':'PASS'},indent=2))
Path('checks.json').write_text(json.dumps({'color_counts':r,'normalized_4x4_backtrack':b,'fold_checks':fold,'assertions':'PASS'},indent=2)+'\n')
