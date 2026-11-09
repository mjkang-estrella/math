from itertools import product
import sys,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];N=int(sys.argv[1]);P=[set(),set()];wit=[{},{}]
def isp(s):return s==s[::-1]
def pals(n):
 for q in product('abc',repeat=(n+1)//2):
  s=''.join(q);yield s+s[:n//2][::-1]
def closure(s):
 for k in range(len(s)+1):
  if isp(s[k:]):return s+s[:k][::-1]
def directive(w):
 v='';u=''
 while len(v)<len(w):
  a=w[len(v)];v=closure(v+a);u+=a
  if not w.startswith(v):return None
 return u
count=0
for size in range(3,N+1):
 for i in range(size-2):
  j=size-3-i
  for a in pals(i):
   for b in pals(j):
    w='a'+a+'b'+b+'c';count+=1
    if not any(isp(w[:k]) and isp(w[k:]) for k in range(1,size)):continue
    if not all(w<w[k:]+w[:k] for k in range(1,size)):continue
    for d,v in enumerate([a,b]):P[d].add(v);wit[d].setdefault(v,w)
 bad=[]
 for w in P[0]&P[1]:
  u=directive(w)
  if u is None or any(c!='b' for c in u[u.find('b'):] if 'b' in u):bad.append({'w':w,'directive':u,'P1_witness':wit[0][w],'P2_witness':wit[1][w]})
 print(size,count,len(P[0]),len(P[1]),len(P[0]&P[1]),bad,flush=True)
 r={'max_witness_word_length':size,'palindromic_factor_pairs_tested':count,'P1_count':len(P[0]),'P2_count':len(P[1]),'intersection_count':len(P[0]&P[1]),'counterexamples':bad}
 (D/f'outputs/palindrome-{N}.json').write_text(json.dumps(r,indent=2)+'\n')
