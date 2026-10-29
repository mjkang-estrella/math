import json,pathlib
from routes import A,add,mul,N
P=pathlib.Path(__file__).resolve().parent
rows=[]
for n in range(1,N+1):
 der=lambda a:[j*v for j,v in enumerate(a)][1:]
 d=add([v*(n+1) for v in mul(der(A[n]),A[n+1])],mul(A[n],der(A[n+1])),-n)
 tail=0;suffix=[]
 for j in range(len(d)-1,-1,-1):tail+=d[j];suffix.append((j,tail))
 neg=[j for j,t in suffix if t<0]
 # Verify exact Abel identity at three rational/integer arguments by independent Horner.
 def val(a,x):
  z=0
  for t in a[::-1]:z=z*x+t
  return z
 for x in [1,2,5]:
  assert val(d,x)==sum((x-1)*t*x**(j-1) for j,t in suffix if j>=1)+sum(d)
 rows.append({'n':n,'negative_suffix_indices':neg,'negative_raw_indices':[j for j,v in enumerate(d) if v<0],'D_at_1':str(sum(d))})
(P/'abel.json').write_text(json.dumps({'rows':rows,'exact_identity_checks':N*3},indent=2))
print(json.dumps({'suffix_failure_n':[r['n'] for r in rows if r['negative_suffix_indices']],'checks':N*3,'n4':rows[3]}))
