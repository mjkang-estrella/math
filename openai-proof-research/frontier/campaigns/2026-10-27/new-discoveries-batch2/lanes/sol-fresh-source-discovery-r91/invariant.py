exec((__import__('pathlib').Path(__file__).parent/'check.py').read_text().split('T=[0,0,0,2,1]')[0])
def sync(a,b):
 a=a+[0]*max(0,len(b)-len(a));b=b+[0]*max(0,len(a)-len(b))
 return lc(a) and lc(b) and all(a[k]*b[k]>=max(a[k-1]*b[k+1],a[k+1]*b[k-1]) for k in range(1,len(a)-1))
def evolve(p,e):return add(p,shift(p),e,shift(e)),add(shift(p,2),e,shift(e),shift(e))
ps=[[a,b,c] for a in range(1,6) for b in range(1,9) for c in range(1,6) if b*b>=a*c]
ob=None;tests=0
for p in ps:
 for e in ps:
  if not sync(p,e):continue
  tests+=1;q,f=evolve(p,e)
  if not sync(q,f):ob={'p':p,'e':e,'Qnext':q,'Enext':f};break
 if ob:break
T=[0,0,0,2,1];Q=[0,0,0,0,1];C=[0,0,0,2,2];fail=None
for n in range(4,101):
 D=[T[k]-(Q[k] if k<len(Q) else 0) for k in range(len(T))]
 assert add(D,shift(D))==C
 if not sync(Q,shift(D)) and fail is None:fail=n
 T,Q,C=update(T,Q,C)
r={'generic_synced_pair_tests':tests,'preservation_obstruction':ob,'actual_reduced_pair_sync_first_failure_through100':fail}
(L/'invariant-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
