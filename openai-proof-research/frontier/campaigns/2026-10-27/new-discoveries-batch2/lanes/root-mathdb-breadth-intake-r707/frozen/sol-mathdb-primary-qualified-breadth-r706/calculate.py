import json,pathlib,math
P=pathlib.Path(__file__).parent
out={'executed':True,'purpose':'bounded screening; neither full-scope proof nor novelty clearance','missing_differences':{}}
for n in [14,15]:
 counts={}
 for mask in range(1<<n):
  dif=0
  for d in range(1,n):
   if mask&(mask>>d):dif+=1
  size=1+2*dif if mask else 0;k=2*n-1-size
  counts[k]=counts.get(k,0)+1
 out['missing_differences'][n]={'total':sum(counts.values()),'counts':counts,'maximizers':[k for k in counts if counts[k]==max(counts.values())]}
assert out['missing_differences'][14]['counts'][2]==out['missing_differences'][14]['counts'][4]
assert out['missing_differences'][15]['maximizers']==[4]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def div(a,b):
 a=a[:];q=[0]*max(1,len(a)-len(b)+1)
 while len(a)>=len(b) and a!=[0]:
  k=len(a)-len(b);v=a[-1]//b[-1];assert v*b[-1]==a[-1];q[k]=v
  for j in range(len(b)):a[k+j]-=v*b[j]
  trim(a)
 return trim(q),a
phis={};poly=[int(i in {0,1,2,3,5,6,8,9,11,12,13,14}) for i in range(15)];rem={}
for b in range(1,61):
 a=[-1]+[0]*(b-1)+[1]
 for d in range(1,b):
  if b%d==0:a,r=div(a,phis[d]);assert r==[0]
 phis[b]=a
 if b>=3 and len(a)-1<=14:
  _,r=div(poly,a);assert r!=[0];rem[b]=r
out['nut_polynomial_remainders']={'range':'3<=b<=60 and phi(b)<=14 ONLY; source totient cutoff not independently replayed','remainders':rem}
out['literal_defects']={'347075':{'n':1,'a1':1,'x':-1,'cdf_X':0.5,'difference':1-(1+math.erf(1/math.sqrt(2)))/2,'note':'At x=-1, discrepancy is 0.5-Phi(-1)=Phi(1)-0.5, equality. At x tending to 1 from below, discrepancy tends to Phi(1)-0.5 as well. At x=1, discrepancy is Phi(-1), smaller. Earlier jump-size shortcut is invalid; no refutation.'},'349368':{'dy_02_power':2**1.5,'sum_dy_01_dy_12':2,'triangle_fails':2**1.5>2}}
(P/'calculations.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'n14':out['missing_differences'][14],'n15':out['missing_differences'][15],'cyclotomic_cases':len(rem),'berry_shortcut':'FAILED; not a counterexample'}))
