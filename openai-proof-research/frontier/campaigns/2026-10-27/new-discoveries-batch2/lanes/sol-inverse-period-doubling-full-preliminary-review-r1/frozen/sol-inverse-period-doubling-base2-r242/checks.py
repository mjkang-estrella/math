from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
T={'S':'S2','2':'34','3':'56','4':'32','5':'35','6':'87','7':'86','8':'88'}
D={q:([0] if q in '26' else []) for q in T}
rows=[]
for m in range(1,12):
 D={q:D[r]+[2**(m-1)+x for x in D[s]] for q,(r,s) in T.items()}
 rows.append({'m':m,'summary':{q:[min(a),max(a),max([y-x for x,y in zip(a,a[1:])],default=0)] if a else None for q,a in D.items()}})
print(json.dumps(rows[:7],indent=1))
w='S'
for _ in range(20):w=''.join(T[x] for x in w)
a=[i for i,q in enumerate(w) if q in '26'];c=[x-j-1 for j,x in enumerate(a)]
F=[0,1]
for _ in range(25):F.append(sum(F[-2:]))
checks=[]
for t in range(3,17):
 p=2**t;j=next(i for i in range(len(c)-1) if c[i+1]-c[i]>p)
 assert (a[j],j,c[j],c[j+1]-c[j])==(5*p-3,2*F[t+2]-2,5*p-2*F[t+2]-2,p+(1 if t%2==0 else 3))
 checks.append({'t':t,'a':a[j],'rank':j,'c':c[j],'distance':c[j+1]-c[j]})
assert all(bool(re.fullmatch(r'(11)*1|1(1|00)*0(11)*1',bin(n)[2:]))==(q in '26') for n,q in enumerate(w) if n)
(L/'checks-result.json').write_text(json.dumps({'block_summaries':rows,'threshold_checks':checks,'language_checks':len(w)-1,'status':'finite diagnostics only'},indent=2))
def expected(q,t):
 p=2**t;e=t%2==0
 return {'S':(1,p-3 if e else p-1,F[t+1]-int(e)),
 '2':(1 if e else 5,p-1 if e else p-3,F[t]+(1 if e else -1)),
 '3':(5 if e else 1,p//2-3 if e else p-1,F[t-1]+(-1 if e else 1)),
 '4':(1 if e else 5,p-3 if e else p-1,F[t]),
 '5':(1 if e else 5,p-3,F[t]-int(not e)),
 '6':(p-1,p-1,1) if e else None,
 '7':None if e else (p-1,p-1,1),'8':None}[q]
for _ in range(505):F.append(sum(F[-2:]))
Q={q:((0,0,1) if q in '26' else None) for q in T}
for t in range(1,501):
 def merge(r,s):
  left,right=Q[r],Q[s];p=2**(t-1)
  if left is None:return None if right is None else (p+right[0],p+right[1],right[2])
  if right is None:return left
  return (left[0],p+right[1],left[2]+right[2])
 Q={q:merge(*T[q]) for q in T}
 if t>=3:
  assert all(Q[q]==expected(q,t) for q in Q)
  assert sum(Q[q][2] for q in ['S','2','3','4','5'])==2*F[t+2]-1
print('summary-recurrence checks t=3..500 PASS; finite checks do not replace induction')
