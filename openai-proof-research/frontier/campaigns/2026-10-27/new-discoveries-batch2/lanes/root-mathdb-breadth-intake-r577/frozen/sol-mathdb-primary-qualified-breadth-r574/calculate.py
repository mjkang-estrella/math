import json,pathlib
P=pathlib.Path(__file__).parent;N=400;fail=[]
for d in range(1,51):
 q=[0]*(N+1);den=[0]*(N+1);den[0]=1;k=0
 while True:
  k+=1;base=3*k+d*k*(k-1)//2
  if base>N:break
  for n in range(k,N+1):den[n]+=den[n-k]
  for n in range(base,N+1):q[n]+=den[n-base]
 Q=[0]*(N+1);Q[0]=1
 for part in range(1,N+1):
  if part!=d and (part-3)%(d+3)==0 or part!=d and (part+3)%(d+3)==0:
   for n in range(part,N+1):Q[n]+=Q[n-part]
 for n in range(1,N+1):
  if q[n]<Q[n]:fail.append([d,n,q[n],Q[n]])
out={'alder':{'executed':True,'d_range':[1,50],'n_range':[1,400],'exact_integer_DP':True,'negative_differences':fail,'scope':'finite diagnostic only; no all-d/all-n proof or eligibility inference'},'farey':{'executed':'exact specialization of read published Theorem B.2, not independent series summation','q':'3/2','published_coefficient':'2^(-1)/Gamma(2)=1/2','record_coefficient':'2/pi','strict_inequality':'pi<4 implies 2/pi>1/2','credit':0,'reason':'source-internal later theorem already defeats literal assertion'}}
(P/'bounded-calculation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
