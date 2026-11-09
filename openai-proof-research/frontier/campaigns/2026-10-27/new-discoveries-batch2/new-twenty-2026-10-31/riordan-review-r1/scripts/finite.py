from pathlib import Path
import runpy,json
D=Path(__file__).resolve().parents[1]
# Load only function definitions, no discovery scripts reused.
s=(D/'scripts/math.py').read_text(); ns={"__file__":str(D/"scripts/math.py")};exec(s[:s.index('x=[-1')],ns);matrix=ns['matrix'];ker=ns['ker']
def iso(a,b):
 n=len(a);da=[sum(r) for r in a];db=[sum(r) for r in b]
 if sorted(da)!=sorted(db):return False
 order=sorted(range(n),key=lambda i:sum(v==da[i] for v in db));assign={};used=set()
 def rec(k):
  if k==n:return True
  i=order[k]
  for j in range(n):
   if j not in used and da[i]==db[j] and all(a[i][u]==b[j][v] for u,v in assign.items()):
    assign[i]=j;used.add(j)
    if rec(k+1):return True
    used.remove(j);del assign[i]
  return False
 return rec(0)
out=[]
for n in range(2,16):
 valid=bad=0;first=None
 for mask in range(1<<(n-2)):
  g=[1]+[(mask>>(i-1))&1 for i in range(1,n-1)]+[0];_,a=matrix(g,n)
  o=[[a[i][j] for j in range(0,n,2)] for i in range(0,n,2)];b=[r[:len(o)] for r in a[:len(o)]]
  if not iso(o,b):continue
  assert all(a[i][j]==0 for i in range(1,n,2) for j in range(1,n,2))
  valid+=1
  if any(any(v[::2]) for v in ker(a)):
   bad+=1
   if first is None:first={'mask':mask,'g':g}
 r={'n':n,'all_binary_prefixes':1<<(n-2),'finite_io_prefixes':valid,'counterexamples':bad,'first':first};out.append(r);print(r,flush=True)
(D/'finite-search.json').write_text(json.dumps(out,indent=2))
