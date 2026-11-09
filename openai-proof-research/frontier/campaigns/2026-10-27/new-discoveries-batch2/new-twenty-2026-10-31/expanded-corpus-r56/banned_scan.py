from pathlib import Path
import json,time
w=Path(__file__).resolve().parent;report=[]
for p,q in [(51,100),(11,20),(3,5),(5,8),(2,3),(7,10),(3,4),(4,5),(9,10)]:
 allowed=[(0,1)];banned=[];counts=[];hit=None
 for n in range(1,21):
  nxt=[];new=[];threshold=p*q**(n-1)
  for bits,num in allowed:
   for d in [0,1]:
    b=2*bits+d;v=q*num-(q-p)*p**(n-1)*(1-d)
    if any((b&((1<<m)-1))==z for m,z in banned):continue
    if b>>(n-1) and v<=threshold:new.append((n,b));continue
    nxt.append((b,v))
  banned+=new
  for m,b in new:
   g=b>>1;double=(g<<(m-1))|g
   for l,z in banned:
    if l<=2*m-2 and any((double>>j)&((1<<l)-1)==z for j in range(2*m-1-l)):
     hit=dict(alpha=format(b,f'0{m}b'),subword=format(z,f'0{l}b'),rho=[p,q])
  counts.append([n,len(nxt),len(new)])
  if hit or len(nxt)>400000:break
  allowed=nxt
 r=dict(rho=[p,q],depth=n,states=counts,banned=[format(z,f'0{m}b').translate(str.maketrans('01','12')) for m,z in banned],hit=hit,limit='20 letters or 400000 states');report.append(r);print(json.dumps(r),flush=True)
(w/'banned-output.json').write_text(json.dumps(report,indent=2))
