import pathlib,itertools,json,sys,sympy as s,random
D=pathlib.Path(__file__).resolve().parents[1];x,l=s.symbols('x l');random.seed(105);out=[]
def test(n,edges,r):
 A=s.zeros(n)
 for a,b in edges:A[a,b]=A[b,a]=1
 B=A.copy();B[r,r]=l;e=s.ones(n,1);cols=[];v=e
 for j in range(n):cols.append(v);v=B*v
 h=s.Poly(s.Matrix.hstack(*cols).det(method='domain-ge'),l)
 if h.is_zero or len(h.terms())!=1 or abs(h.LC())!=1:return None
 Ar=A.minor_submatrix(r,r);res=s.resultant(A.charpoly(x).as_expr(),Ar.charpoly(x).as_expr(),x)
 if abs(res)!=1:return None
 d1=A.det();d2=Ar.det()
 if not((abs(d1)==1 and d2==0)or(d1==0 and abs(d2)==1)):return None
 return dict(n=n,edges=edges,root=r,h=str(h.as_expr()),exponent=h.degree(),expected=n//2,holds=h.degree()==n//2)
mode=sys.argv[1];tested=0
if mode=='small':
 for n in range(1,5):
  pairs=list(itertools.combinations(range(n),2))
  for mask in range(1<<len(pairs)):
   E=[e for i,e in enumerate(pairs)if mask>>i&1]
   for r in range(n):
    z=test(n,E,r);tested+=1
    if z:out.append(z)
  print(n,tested,len(out),flush=True);(D/'outputs/rooted-small.json').write_text(json.dumps(dict(tested=tested,sufficient_preservers=out),indent=2))
else:
 for n in range(11,15):
  E=[(i,i+1)for i in range(n-1)]
  for r in [0,n//2]:
   z=test(n,E,r);tested+=1
   if z:out.append(z)
   print(n,r,z and z['h'],flush=True);(D/'outputs/rooted-large.json').write_text(json.dumps(dict(tested=tested,sufficient_preservers=out),indent=2))
