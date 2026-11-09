from pathlib import Path
import json,itertools,random
D=Path(__file__).resolve().parents[1];rows=[];rng=random.Random(103)
for q in range(11,501,8):
 if any(q%p==0 for p in range(2,int(q**.5)+1)):continue
 n=q+1;res={i*i%q for i in range(1,q)}
 H=[[1]*n]+[[1]+[-1 if j==i else (1 if (i-j)%q in res else -1) for j in range(q)] for i in range(q)]
 assert all(sum(a*b for a,b in zip(H[i],H[j]))==0 for i in range(n) for j in range(i))
 witness=None;tries=0
 for trial in range(200):
  cols=list(range(1,9)) if trial==0 else rng.sample(range(1,n),8);bits=[sum((H[i][j]==1)<<i for i in range(n)) for j in cols]
  xor=[0]*256
  for s in range(1,256):lb=s&-s;xor[s]=xor[s^lb]^bits[lb.bit_length()-1]
  balanced=[s for s in range(256) if s.bit_count()>=3 and xor[s].bit_count()==n//2]
  tries+=1
  for v,w in itertools.combinations(balanced,2):
   if not v&~w or not w&~v or ((v^w).bit_count()==2):continue
   if (xor[v]&xor[w]).bit_count()==n//4:witness=dict(columns=cols,V=v,W=w);break
  if witness:break
 rows.append(dict(order=n,m=n//4,trials=tries,witness=witness))
 print(rows[-1],flush=True)
(D/'outputs/hadamard.json').write_text(json.dumps(rows,indent=2)+'\n')
