from pathlib import Path
import json

def coeffs(n,k,N):
    # Exact coefficients of q^(-2n-1)(G_{k,n}-G_{k+1,n-1}).
    a=[1]+[0]*N
    for d in range(1,2*n+2,2):
        for i in range(d,N+1):a[i]+=a[i-d]
    for d in [2*(k-n-1)]+list(range(2*k+1,2*k+2*n-1,2)):
        if not d:return [0]*(N+1)
        for i in range(N,d-1,-1):a[i]-=a[i-d]
    return a

N=1200;tested=0;hit=None
for n in range(1,41):
    for delta in range(1,41):
        k=n+1+delta;a=coeffs(n,k,N);tested+=1
        if min(a)<0:
            hit={'n':n,'k':k,'shifted_degree':next(i for i,v in enumerate(a) if v<0),'coefficient':min(a)};break
    if hit:break
result={'scope':'Finite exact prefix only; not full coefficient positivity or proof','tested_parameter_pairs':tested,'shifted_degree_max':N,'first_negative':hit,'ordinary_proof_complete':False,'discovery_credit':0}
Path(__file__).with_name('monotonicity-prefix.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
