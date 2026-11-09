import json,pathlib,itertools,math
D=pathlib.Path(__file__).resolve().parents[1];N=50000;data=(D/'outputs/partition-parities.bin').read_bytes();e=data[:N+1];o=data[N+1:];rows=[]
for p in range(5,1001):
 if p%24 not in (1,7) or any(p%d==0 for d in range(2,math.isqrt(p)+1)):continue
 witnesses=[]
 for j in [1,4,8]:
  for y in range(math.isqrt(j*p//216)+1):
   x=math.isqrt(j*p-216*y*y)
   if x*x+216*y*y==j*p and math.gcd(x,y)==1:witnesses.append([j,x,y])
 if not witnesses:continue
 inv=pow(24,-1,p)-p;bad=[];checked=0
 for a in range(p):
  if a==p//24:continue
  n=max(0,(inv-p*a+p*p-1)//(p*p))
  while 2*(p*p*n+p*a-inv)<=N:
   idx=2*(p*p*n+p*a-inv);checked+=1
   if e[idx] or o[idx]:bad.append([n,a,idx,e[idx],o[idx]])
   n+=1
 rows.append(dict(p=p,witnesses=witnesses,checked=checked,failures=bad))
print(json.dumps(rows,indent=2));(D/'outputs/progression-source.json').write_text(json.dumps(rows,indent=2))
# Verify the public 13/21 subspace count, without claiming it as discovery.
W=lambda a,b:frozenset([0,8^a,8^b,a^b])
w=W(1,2);spaces={W(a,b) for a,b in itertools.combinations(range(1,8),2)};good=sum(len(w&s)>1 for s in spaces)
r=dict(subspaces=len(spaces),nontrivial_intersections=good,ratio=f'{good}/{len(spaces)}',novel=False);print(r);(D/'outputs/suborbit-prior-check.json').write_text(json.dumps(r,indent=2))
