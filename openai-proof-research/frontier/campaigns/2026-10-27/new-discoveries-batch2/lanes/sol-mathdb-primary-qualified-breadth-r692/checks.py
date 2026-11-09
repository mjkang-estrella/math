import pathlib,json,itertools,functools
P=pathlib.Path(__file__).resolve().parent
n=6;N=4*n
B=set()
for i in range(1,N+1):
 for j in range(i+1,N+1):
  if (4<=i<=2*n-3 and 2*n+4<=j<=4*n-3) or (i in (1,2) and 2*n+4<=j<=4*n) or (1<=i<=2*n-3 and j in (4*n,4*n-1)) or (3<=i<=9 and 2*n-2<=j<=2*n) or (2*n+1<=i<=2*n+3 and 4*n-8<=j<=4*n-2) or (i,j) in [(3,2*n+1),(2*n,4*n-2)]:B.add((i,j))
tri=[t for t in itertools.combinations(range(1,N+1),3) if all(e in B for e in itertools.combinations(t,2))]
@functools.lru_cache(None)
def nest(a,b):
 if a>=b:return 0
 return max(nest(a+1,b),max((1+nest(a+1,j-1) for j in range(a+1,b+1) if (a,j) not in B),default=0))
assert not tri and nest(1,N)<n
count=0
for mask in range(1<<9):
 E={(x,y) for x in range(3) for y in range(3) if mask>>(3*x+y)&1}
 if any(not any(a==x for a,b in E) for x in range(3)) or any(not any(b==y for a,b in E) for y in range(3)):continue
 D={0,1,2}
 for x in range(3):
  if all(any((a,y) in E for a in D-{x}) for y in range(3)):D.remove(x)
 M={}
 for x in D:
  p=next(y for y in range(3) if {a for a in D if (a,y) in E}=={x});M[(x,p)]=1
 for y in range(3):
  if not any(b==y for a,b in M):M[(next(a for a in D if (a,y) in E),y)]=2
 colors={e:M.get(e,3) for e in E}
 for x,y in E:
  vals=[c for (a,b),c in colors.items() if a==x or b==y];assert any(vals.count(c)==1 for c in vals)
 count+=1
out={'nested_matching':{'source':'arXiv:2201.07637v1 Section3.2','n':n,'vertices':N,'blue_edges':len(B),'blue_triangles':len(tri),'maximum_red_nested_matching':nest(1,N),'conclusion':'Published witness defeats 4n-1; no new credit.'},'conflict_free':{'source':'arXiv:2604.24183v1 Theorem1.3','checked_labeled_3_by_3_no_isolated_graphs':count,'passed':True,'limit':'Finite implementation check of published construction, not a new proof or all-graph computation.'}}
(P/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
