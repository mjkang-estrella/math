from pathlib import Path
import itertools,json,random
D=Path(__file__).resolve().parents[1]
def reduced(n,limit=None):
 rows=[tuple(range(n))];cols=[1<<i for i in range(n)];count=0
 perms={i:[p for p in itertools.permutations(range(n)) if p[0]==i] for i in range(1,n)}
 def rec(r):
  if r==n:yield tuple(rows);return
  for p in perms[r]:
   if any(cols[c]>>p[c]&1 for c in range(n)):continue
   rows.append(p)
   for c in range(n):cols[c]|=1<<p[c]
   yield from rec(r+1)
   for c in range(n):cols[c]^=1<<p[c]
   rows.pop()
 for t in rec(1):
  yield t;count+=1
  if limit and count>=limit:return
def comps(s,n):
 if n==1:yield(s,);return
 for a in range(s+1):
  for t in comps(s-a,n-1):yield (a,)+t
def profiles(t):
 n=len(t);out=set()
 for omitted in range(n):
  rs=[r for r in range(n) if r!=omitted]
  for cs in itertools.permutations(range(n),n-1):
   a=[0]*n
   for r,c in zip(rs,cs):a[t[r][c]]+=1
   out.add(tuple(a))
 return out
out=[]
for n in range(6,8):
 count=0;fails=[];total=set(comps(n-1,n));limit=None if n<=6 else 120
 for t in reduced(n,limit):
  count+=1;missing=total-profiles(t)
  if missing:fails.append({'table':t,'missing':sorted(missing)});break
 row={'n':n,'reduced_latin_squares':count,'enumeration':'complete' if n<=6 else 'first 120 lexicographic, not exhaustive','profiles_per_square':len(total),'failures':fails};out.append(row);print(row,flush=True)
(D/'matching-extend.json').write_text(json.dumps(out,indent=2)+'\n')
