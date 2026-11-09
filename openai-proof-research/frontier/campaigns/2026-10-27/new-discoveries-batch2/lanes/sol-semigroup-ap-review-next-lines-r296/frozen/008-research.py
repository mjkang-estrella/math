from pathlib import Path
from math import gcd
import json
L=Path(__file__).resolve().parent
def apery(a,t):
 A=[0]*a
 for j in range(a): A[j*t%a]=((j+1)//2)*a+j*t
 return A
def rank(A,n): return sum(max(0,1+(n-x)//len(A)) for x in A)-1
def witness(a,t):
 A=apery(a,t); F=max(A)-a
 # Exact finite endpoint for diagnostics, not a universal bounded scan.
 seq=[n for n in range(1,F+4) if n>=A[n%a]]
 return next(((i+1,seq[i:i+3]) for i in range(0,len(seq)-2,3) if len({n%3 for n in seq[i:i+3]})<3),None)
if __name__=='__main__':
 rows=[]
 for a,t in [(101,4),(103,4),(104,3),(100,3),(31,4),(37,4),(41,4),(23,4),(17,4),(25,4),(29,4),(101,7),(101,10),(53,4),(55,4)]:
  if gcd(a,t)==1: rows.append(dict(a=a,t=t,witness=witness(a,t),F=max(apery(a,t))-a))
 (L/'diagnostic.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps(rows))
