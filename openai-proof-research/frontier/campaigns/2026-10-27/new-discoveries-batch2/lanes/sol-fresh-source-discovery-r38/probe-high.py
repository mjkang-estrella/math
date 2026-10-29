import resource,signal,math,json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
b=Path(__file__).parent
B=[]
for n in range(1,37):
 num=sum(2*math.comb(n+1,k-1)*math.comb(n+1,k)*math.comb(n+1,k+1) for k in range(1,n+1))
 den=n*(n+1)**2
 assert num%den==0
 B.append(num//den)
a=B; rows=[]
for r in range(1,17):
 a=[a[i]*a[i+2]-a[i+1]**2 for i in range(len(a)-2)]
 neg=[i+1 for i,x in enumerate(a) if x<0]
 rows.append(dict(r=r,n_max=len(a),negative_indices=neg,max_bits=max(x.bit_length() for x in a)))
 if neg:break
(b/'probe-high-results.json').write_text(json.dumps(rows,indent=2)+'\n')
print(rows)
