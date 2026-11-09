import math,json
out=[]
for q in range(5,102,2):
 v=q*q;count=0;examples=[]
 for k in range(4,v-1,2):
  for g in range(1,2*(k-1)//(q+1)+1):
   r=2*(q-1)*g
   if r*(k-1)%(v-1) or v*r%k:continue
   lam=r*(k-1)//(v-1)
   if math.gcd(r,2*lam)!=g or lam<g*g:continue
   count+=1
   if len(examples)<3:examples.append([v,v*r//k,r,k,lam])
 out.append({'q':q,'candidate_parameter_tuples':count,'examples':examples})
open('outputs/design-parameters.json','w').write(json.dumps(out,indent=2));print('q=5..101 odd; necessary parameter candidates',sum(x['candidate_parameter_tuples'] for x in out));print(out[-1])
