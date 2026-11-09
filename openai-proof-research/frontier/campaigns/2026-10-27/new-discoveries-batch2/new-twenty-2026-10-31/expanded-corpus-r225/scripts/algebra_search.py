import math,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
def parts(n,m=None):
 if not n:yield ();return
 for k in range(min(n,n if m is None else m),1-1,-1):
  for p in parts(n-k,k):yield (k,)+p
def dim(p):
 h=1
 for i,r in enumerate(p):
  for j in range(r):h*=r-j+sum(q>j for q in p[i+1:])
 return math.factorial(sum(p))//h
def transpose(p):return tuple(sum(x>j for x in p) for j in range(p[0]))
def immersion():
 out=[]
 for n in range(5,46):
  if n in (6,7,8):continue
  bound=n*(n-3)//2;expected={(n,),(n-1,1),(n-2,2),(1,)*n,(2,)+(1,)*(n-2),(2,2)+(1,)*(n-4)}
  low=[];extra=[];count=0
  for p in parts(n):
   count+=1;f=dim(p)
   if f<=bound:
    low.append([p,f])
    if p not in expected:extra.append([p,f])
  row={'n':n,'partitions':count,'dimension_bound':bound,'low_dimension':low,'extra_beyond_six_source_shapes':extra};out.append(row);print(json.dumps(row),flush=True)
 (D/'immersion-dimensions.json').write_text(json.dumps(out,indent=2)+'\n')
def trim(p):
 while p and not p[-1]:p.pop()
 return p
def primitive(p):
 p=trim(p)
 if p:
  g=math.gcd(*p);p=[x//g for x in p]
 return p
def rem(a,b):
 a=a[:]
 while len(a)>=len(b):
  lc=b[-1];c=a[-1];d=len(a)-len(b);a=[abs(lc)*x for x in a]
  for j,x in enumerate(b):a[j+d]-=(1 if lc>0 else -1)*c*x
  a=primitive(a)
 return a
def sturm(p):
 while p and p[0]==0:p=p[1:]
 p=primitive(p);q=primitive([i*p[i] for i in range(1,len(p))]);seq=[p,q]
 while q:
  r=[-x for x in rem(p,q)]
  if not r:break
  seq.append(r);p,q=q,r
 def variations(signs):return sum(a!=b for a,b in zip(signs,signs[1:]))
 lo=[(1 if a[-1]>0 else -1)*(-1)**(len(a)-1) for a in seq if a];hi=[1 if a[-1]>0 else -1 for a in seq if a]
 return {'degree_after_zero_removal':len(seq[0])-1,'distinct_real_nonzero_roots':variations(lo)-variations(hi),'gcd_degree':len(seq[-1])-1}
def roots():
 A=[1];out=[]
 for n in range(2,151):
  A=[(k+1)*(A[k] if k<len(A) else 0)+(n-k)*(A[k-1] if k else 0) for k in range(n)]
  if n<5:continue
  row={'n':n}
  for sign,name in [(1,'even'),(-1,'odd')]:
   p=[(a+sign*(-1)**k*math.comb(n-1,k))//2 for k,a in enumerate(A)];row[name]=sturm(p)
  out.append(row);print(json.dumps(row),flush=True)
  if any(v['distinct_real_nonzero_roots']!=v['degree_after_zero_removal'] and not v['gcd_degree'] for v in [row['even'],row['odd']]):print('FAILURE',row,flush=True);break
 (D/'excedance-sturm.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':immersion() if sys.argv[1]=='immersion' else roots()
