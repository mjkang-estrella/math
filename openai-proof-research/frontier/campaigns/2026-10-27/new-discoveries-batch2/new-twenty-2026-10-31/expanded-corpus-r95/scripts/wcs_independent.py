import json,pathlib,math
L=pathlib.Path(__file__).resolve().parents[1];k=22
sigma=[22,3,4,5,6,7,8,9,10,13,12,11,14,15,16,17,18,19,20,21,2,1]
viol=[(i,j,d) for i in range(k) for j in range(k) for d in range(1,k+1) if sigma[i]%d==0 and (i-j)%d==0 and sigma[j]%d!=0]
ns={};exec((L/'scripts/wcs.py').read_text().split('for k in range(501,1001):')[0],ns)
starts=ns['seeds'](k);closure={tuple(s) for _,s in starts};q=list(closure)
while q:
 s=q.pop();t=tuple(16 if v==8 else 8 if v==16 else v for v in s)
 for u in [s[::-1],t]:
  if u not in closure:closure.add(u);q.append(u)
power_swaps=[]
for p in range(2,23):
 if ns['prime'](p):
  for c in range(1,7):
   if p**c<=22<p**c+p**(c-1):power_swaps.append([p,c,p**c,p**(c-1)])
print(json.dumps({'k':k,'sigma':sigma,'is_permutation':sorted(sigma)==list(range(1,k+1)),'literal_triples_tested':k**3,'WCS_violations':viol,'starts':starts,'prime_power_swaps':power_swaps,'literal_closure':sorted(closure),'closure_size':len(closure),'witness_in_closure':tuple(sigma) in closure,'qualification':'source-internal mismatch; no discovery credit'}))
