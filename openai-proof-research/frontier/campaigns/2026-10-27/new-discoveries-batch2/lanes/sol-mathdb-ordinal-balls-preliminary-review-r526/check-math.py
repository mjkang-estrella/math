"""Independent read-only stdout checker. No producer code import or execution."""
import itertools,json
R=((0,1,3,4),(1,0,5,6),(3,5,0,2),(4,6,2,0))
def balls(d):
 result=set();by=[]
 for c,row in enumerate(d):
  sp=set(row); here=set()
  for k in range(1,1<<len(sp)):
   vals=list(sorted(sp));A={v for i,v in enumerate(vals) if k>>i&1};B=sp-A
   if all(a<b for a in A for b in B):here.add(tuple(i for i,v in enumerate(row) if v in A))
  by.append(sorted(here,key=lambda s:(len(s),s)));result|=here
 return result,by
expected={(0,),(1,),(2,),(3,),(0,1),(2,3),(0,1,2),(0,2,3),(0,1,2,3)}
b,by=balls(R);assert b==expected and len(b)==9<4*5//2
assert set(sum((list(r) for r in R),[]))==set(range(7))
assert all(R[i][j]==R[j][i] and ((R[i][j]==0)==(i==j)) for i in range(4) for j in range(4))
M=tuple(tuple(0 if i==j else 10+R[i][j] for j in range(4)) for i in range(4))
assert all(M[i][j]<=M[i][k]+M[k][j] for i,j,k in itertools.product(range(4),repeat=3));assert balls(M)[0]==b
# Explicit-radius control, all possible threshold equivalence classes.
assert {tuple(i for i in range(4) if R[c][i]<=r) for c in range(4) for r in range(7)}==b
# Mutations must change the reference or conventions.
mut=[list(r) for r in R];mut[0][2],mut[0][3]=mut[0][3],mut[0][2];mut[2][0],mut[3][0]=mut[3][0],mut[2][0]
assert balls(mut)[0]!=expected
assert b-{(0,1,2)}!=expected and b|{()}!=expected and b-{(0,1,2,3)}!=expected
# Source Example 6.2 with 29 distinct balls and its complete six rows.
S=((0,5,12,15,8,6),(5,0,4,11,14,7),(12,4,0,3,10,13),(15,11,3,0,2,9),(8,14,10,2,0,1),(6,7,13,9,1,0))
s,sby=balls(S);assert len(s)==29
expected_orders=((0,1,5,4,2,3),(1,2,0,5,3,4),(2,3,1,4,0,5),(3,4,2,5,1,0),(4,5,3,0,2,1),(5,4,0,1,3,2))
assert all(set(sby[c])=={tuple(sorted(order[:k])) for k in range(1,7)} for c,order in enumerate(expected_orders))
# Figure 2 interval-family convention control using generic line points 0,1,4,10.
line=tuple(tuple(abs(x-y) for y in (0,1,4,10)) for x in (0,1,4,10));assert len(balls(line)[0])==10
# The reported 720/48 statistics are auxiliary, not used in the proof.
counts={};edges=list(itertools.combinations(range(4),2))
for order in itertools.permutations(range(1,7)):
 d=[[0]*4 for _ in range(4)]
 for (i,j),r in zip(edges,order):d[i][j]=d[j][i]=r
 n=len(balls(d)[0]);counts[n]=counts.get(n,0)+1
assert sum(counts.values())==720 and counts[9]==48
print(json.dumps(dict(status='PASS',balls=sorted(b,key=lambda s:(len(s),s)),centered=by,metric=M,source_example_count=len(s),source_example_rows=sby,negative_controls=['changed order','omitted triple','extra empty','omitted full'],order_histogram=counts),indent=2))
