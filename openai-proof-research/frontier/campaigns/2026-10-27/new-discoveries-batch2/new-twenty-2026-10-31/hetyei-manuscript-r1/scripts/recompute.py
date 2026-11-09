"""Fresh manuscript arithmetic; standard library only. No supplied code is executed."""
from pathlib import Path
from functools import cache
from itertools import product
from fractions import Fraction
import json,csv
R=Path(__file__).resolve().parent.parent
O=R/'computations';O.mkdir(exist_ok=True)
def add(p,q,k=1):
 d=p.copy()
 for w,c in q.items():d[w]=d.get(w,0)+k*c
 return {w:c for w,c in d.items() if c}
def mul(p,q):
 d={}
 for u,c in p.items():
  for v,e in q.items():d[u+v]=d.get(u+v,0)+c*e
 return {w:c for w,c in d.items() if c}
def rev(p):return {w[::-1]:c for w,c in p.items()}
def cuts(w):return [(w[:i],w[i+1:]) for i in range(len(w))]
@cache
def mixpart(r,s,k,u,v,printed=False):
 if k<2 or (k-r-s-1)%2:return {}
 if k==2:
  if (r,s)==(1,2):return {u+'a'+v:1}
  if (r,s)==(2,1):return {(u+'b'+v if printed else v+'b'+u):1}
  return {}
 d={}
 for pre,post in cuts(u if r==1 else v):
  q=mixpart(3-r,s,k-1,post if r==1 else u,v if r==1 else post,printed)
  d=add(d,{pre+('a' if r==1 else 'b')+w:c for w,c in q.items()})
 return d
@cache
def mix(u,v,printed=False):
 d={}
 for r,s in product((1,2),repeat=2):
  for k in range(2,len(u)+len(v)+3):d=add(d,mixpart(r,s,k,u,v,printed))
 return d
@cache
def image(w,printed=False):
 d=add({w:1},{w[::-1]:1})
 for u,v in cuts(w):d=add(d,mix(u[::-1],v,printed))
 return d
def transform(p,printed=False):
 d={}
 for w,c in p.items():d=add(d,image(w,printed),c)
 return d
def words(n):return [''.join(x) for x in product('ab',repeat=n)]
def eliminate(A):
 A=[[Fraction(x) for x in row] for row in A];piv=[];steps=[];r=0
 for j in range(len(A[0])):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[i],A[r]=A[r],A[i];v=A[r][j];steps.append([i,r,j,str(v)])
  A[r]=[x/v for x in A[r]]
  for k in range(len(A)):
   if k!=r and A[k][j]:
    v=A[k][j];A[k]=[x-v*y for x,y in zip(A[k],A[r])]
  piv.append(j);r+=1
  if r==len(A):break
 return r,piv,A,steps
u={'aaaba':1,'aaabb':1,'aabaa':-2,'aabba':-1,'aabbb':1,'abaaa':1,'abaab':1,'abbaa':-1,'abbab':1,'abbba':-2,'baaab':-2,'baaba':1,'baabb':-1,'babba':1,'babbb':1,'bbaaa':1,'bbaab':-1,'bbabb':-2,'bbbaa':1,'bbbab':1}
assert u==json.loads((R/'evidence/expanded-corpus-r240/outputs/hetyei-certificates-v2.json').read_text())['A']['u']
assert rev(u)==u and u['aaaba']==1 and not transform(u)
W=words(5)
with (O/'certificate-contributions.tsv').open('w') as f:
 wr=csv.writer(f,delimiter='\t');wr.writerow(['input','coefficient']+W)
 for w,c in u.items():wr.writerow([w,c]+[c*image(w).get(v,0) for v in W])
 wr.writerow(['TOTAL','']+[transform(u).get(v,0) for v in W])
table=[]
for n in range(1,8):
 W=words(n);A=[[image(w).get(v,0) for w in W] for v in W]
 rk,piv,rr,steps=eliminate(A)
 anti=sum(w<w[::-1] for w in W)
 assert all(image(w)==image(w[::-1]) for w in W)
 row=dict(n=n,ambient=len(W),rank=rk,kernel=len(W)-rk,anti=anti,symmetric_kernel=len(W)-rk-anti)
 table.append(row)
 (O/f'matrix-{n}.json').write_text(json.dumps(dict(words=W,matrix=A,pivot_columns=piv,elimination_pivots=steps,rref=[[str(x) for x in r] for r in rr]),indent=1)+'\n')
 print(row,flush=True)
assert [r['kernel'] for r in table]==[0,1,2,6,13,30,63]
# Direct flag enumeration for arbitrary finite bounded graded posets.
def psi(level,le):
 top=max(range(len(level)),key=lambda i:level[i]);bot=min(range(len(level)),key=lambda i:level[i]);n=level[top]-1
 # enumerate chains of proper elements; selected ranks yield flag f weights.
 d={}
 def visit(last,sel):
  nonlocal d
  p={'':1}
  for k in range(1,n+1):p=mul(p,{'b':1} if k in sel else {'a':1,'b':-1})
  d=add(d,p)
  for j in range(len(level)):
   if j!=top and level[j]>level[last] and le(last,j):visit(j,sel|{level[j]})
 visit(bot,set());return d
# D(n,S): complete comparability between ranks; rank sizes 2 in S, 1 otherwise.
def doubled(n,mask):
 level=[0]+[k for k in range(1,n+1) for _ in range(1+((mask>>(k-1))&1))]+[n+1]
 return level,lambda i,j:i==j or level[i]<level[j]
def direct_total(level,le):
 d={};N=len(level)
 for x in range(N):
  intervals=[(i,j) for i in range(N) for j in range(N) if le(i,x) and le(x,j)]
  ranks=[level[j]-level[i] for i,j in intervals]
  def incl(p,q):
   i,j=intervals[p];k,l=intervals[q];return le(k,i) and le(j,l)
  d=add(d,psi(ranks,incl))
 return d
posets=[]
for n in range(1,6):
 W=words(n);indices=[];bad=0
 for mask in range(2**n):
  lv,le=doubled(n,mask);p=psi(lv,le);indices.append([p.get(w,0) for w in W])
  assert direct_total(lv,le)==transform(p)
 rank=eliminate(indices)[0];assert rank==2**n
 posets.append(dict(degree=n,posets=2**n,span_rank=rank,mismatches=bad))
 print('Poset spanning test',posets[-1],flush=True)
# Misprint and companion checks, all used explicitly in the manuscript.
printed=transform({'ab':1,'ba':-1},True);assert printed=={'ab':2,'ba':-2}
s=transform({'aab':1,'baa':1});assert s!=rev(s)
p={'aa':1,'ab':2,'ba':2,'bb':1};assert transform(p)=={w:8*c for w,c in p.items()}
L=add(mul({'a':1,'b':-1},p),mul(p,{'a':1,'b':-1}))
defect=add(transform(L),L,-8);assert defect=={'aba':-12,'abb':-12,'baa':12,'bab':12}
result=dict(table=table,certificate=u,certificate_terms=len(u),certificate_degree=5,certificate_coefficient_l1=sum(map(abs,u.values())),certificate_image=transform(u),certificate_image_column_sums=sorted({sum(image(w).values()) for w in u}), unweighted_unit_terms=len(u)*sum(image(next(iter(u))).values()),weighted_unit_terms=sum(abs(c)*sum(image(w).values()) for w,c in u.items()),poset_tests=posets,printed_degree_two=printed,M_a_1_ER=mix('a',''),M_a_1_printed=mix('a','',True),remark_s_image=s,lemma_defect=defect)
(O/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
