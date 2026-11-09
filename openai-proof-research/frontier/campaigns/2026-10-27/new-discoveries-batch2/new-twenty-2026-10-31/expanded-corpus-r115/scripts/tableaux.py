import itertools,math,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];records=[]
for n in range(3,8):
 for a in range(2,n):
  for b in range(2,n):
   t=n-a-b+1
   if t<0:continue
   gamma=(a,)+(2,)*t+(b,);edges=set();s=0
   for g in gamma:
    edges.update(itertools.combinations(range(s,s+g),2));s+=g-1
   lt=lambda x,y:x<y and (x,y) not in edges
   words={}
   for l in range(1,n+1):
    for w in itertools.permutations(range(n),l):
     if any(lt(y,x) for x,y in zip(w,w[1:])):continue
     if any(all(lt(w[i],v) for v in w[i+1:]) for i in range(l-1)):continue
     words.setdefault(sum(1<<v for v in w),[]).append(w)
   counts={};arrays=[0]
   def grow(rows,used):
    if used==(1<<n)-1:
     arrays[0]+=1;shape=tuple(sorted(map(len,rows),reverse=True));counts[shape]=counts.get(shape,0)+1;return
    remain=((1<<n)-1)^used;mask=remain
    while mask:
     for w in words.get(mask,[]):
      if all(all(lt(r[j],w[j]) for j in range(min(len(r),len(w)))) and all(lt(r[-1],w[j]) for j in range(len(r),len(w))) for r in rows):grow(rows+[w],used|mask)
     mask=(mask-1)&remain
   grow([],0)
   checks=[]
   for colors in range(n+1):
    # clique chain chromatic polynomial: first clique falling factorial; each successive clique shares one vertex
    lhs=math.prod(colors-i for i in range(a))
    for g in gamma[1:]:lhs*=math.prod(colors-1-i for i in range(g-1))
    rhs=sum(c*math.prod(math.comb(colors,l) if colors>=l else 0 for l in shape) for shape,c in counts.items())
    checks.append(lhs==rhs)
   row=dict(n=n,gamma=gamma,powerful_arrays=arrays[0],q=1,specializations=list(range(n+1)),identity_holds=all(checks));records.append(row);print(row,flush=True)
   (D/'outputs/tableaux.json').write_text(json.dumps(records,indent=2)+'\n')
   if not all(checks):raise SystemExit('failure')
