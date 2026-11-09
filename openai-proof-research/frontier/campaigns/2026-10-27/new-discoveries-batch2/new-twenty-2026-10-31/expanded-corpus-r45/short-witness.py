from diagnostics import *
best=None;count=0
for t in range(1,301):
 for u in range(1,t+1):
  D=t*t+4*u;s=math.isqrt(D)
  if s*s==D:continue
  m,d=t,2;seen=set();a=[];states=[]
  while (m,d) not in seen:
   seen.add((m,d));states.append([m,d]);z=(m+s)//d;a.append(z);m=z*d-m;d=(D-m*m)//d
  for k,v in enumerate(sorted(set(a),reverse=True),1):
   if k*v>t:
    count+=1
    if best is None or len(a)<len(best['a']):best={'t':t,'u':u,'D':D,'a':a,'states':states,'rank':k,'value':v};print(json.dumps(best),flush=True)
print(json.dumps({'violating_rank_instances':count,'best':best}))
(O/'witness.json').write_text(json.dumps(best,indent=2))
