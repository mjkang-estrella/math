"""Read-only independent source-restriction deduction, no producer imports."""
import json
# Literal Example 6.2 order a,b,e,f.
D=((0,5,8,6),(5,0,14,7),(8,14,0,1),(6,7,1,0))
# Direct threshold approach; finite cut completeness proved in review.md.
rows=[];bs=set()
for c in range(4):
 here=[]
 for r in sorted(set(D[c])):
  s=tuple(i for i in range(4) if D[c][i]<=r);here.append(s);bs.add(s)
 rows.append(here)
expected={(0,),(1,),(2,),(3,),(0,1),(2,3),(0,1,3),(0,2,3),(0,1,2,3)}
assert bs==expected and len(bs)==9
assert sorted(D[i][j] for i in range(4) for j in range(i+1,4))==[1,5,6,7,8,14]
# Relabel to producer witness order: source f,e,a,b -> 0,1,2,3.
perm=(3,2,0,1);ranks={0:0,1:1,5:2,6:3,7:4,8:5,14:6}
normalized=[[ranks[D[i][j]] for j in perm] for i in perm]
assert normalized==[[0,1,3,4],[1,0,5,6],[3,5,0,2],[4,6,2,0]]
print(json.dumps(dict(status='PASS',source='Example 6.2 table (6.1)',restriction=['a','b','e','f'],matrix=D,centered_rows=rows,balls=sorted(bs,key=lambda s:(len(s),s)),relabel=['f','e','a','b'],normalized=normalized,conclusion='Source restriction is exactly isomorphic to producer witness'),indent=2))
