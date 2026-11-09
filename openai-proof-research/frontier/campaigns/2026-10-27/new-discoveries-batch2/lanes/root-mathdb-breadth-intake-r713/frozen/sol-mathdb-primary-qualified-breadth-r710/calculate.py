from pathlib import Path
import json,itertools,math
P=Path(__file__).parent;out={}
# Exact integer product of ((1+x^k)/(1-x^k))^q truncated at degree 7.
counts={}
for q in [2,3,5,7,11,13]:
 a=[1]+[0]*7
 for k in range(1,8):
  for color in range(q):
   b=a[:]
   for n in range(k,8):b[n]+=a[n-k]
   for n in range(k,8):b[n]+=b[n-k]
   a=b
 counts[q]={'coefficients':a,'all_seven_residues_zero':all(a[i]%m==0 for i,m in enumerate([1,2,4,8,2,8,8,32]) if i)}
out['357317']={'scope':'n=0 only; selected primes only; no universal conclusion','counts':counts}
# Directed relation rewrites use x -> A*x+B*y and y -> C*x+D*y.
paths=[[(1,0),(3,1),(4,3),(5,5)],[(0,1),(1,3),(3,4),(5,5)]]
for path in paths:
 for a,b in zip(path,path[1:]):
  assert (a[0]>0 and b==(a[0]+2,a[1]+1)) or (a[1]>0 and b==(a[0]+1,a[1]+2))
out['357705']={'A':3,'B':1,'C':1,'D':3,'paths':paths,'equal_row_sums':True,'credit':'excluded source-context/domain correction'}
rows=[]
for m in [3,4,5]:
 for n in range(1,8):
  counts=[0,0]
  for pi in itertools.permutations(range(1,n+1)):
   inv=[pi.index(k) for k in range(1,n+1)]
   if any(inv[i-1]<inv[i]>inv[i+1] for i in range(1,n-1)):continue
   pat=(2,1)+tuple(range(3,m+1))
   def std(t):return tuple(sorted(t).index(x)+1 for x in t)
   classical=any(std(t)==pat for t in itertools.combinations(pi,m))
   consecutive=any(std(pi[i:i+m])==pat for i in range(n-m+1))
   counts[0]+=not classical;counts[1]+=not consecutive
  f=sum((-1)**j*math.comb(n-(m-2)*j-1,n-(m-1)*j-1)*2**(n-(m-1)*j-1) for j in range((n-1)//(m-1)+1))
  rows.append({'m':m,'n':n,'classical':counts[0],'consecutive':counts[1],'formula':f})
out['356229']={'scope':'n<=7,m in3..5; no proof for unbounded parameters','rows':rows}
(P/'bounded-calculations.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
