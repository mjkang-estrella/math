import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for s in range(128):
 S={d for i in range(7) if s>>i&1 for d in [i+1,14-i]}
 adj=lambda a,b:(b-a)%15 in S
 tri=next(((a,b) for a,b in itertools.combinations(range(1,15),2) if adj(0,a) and adj(0,b) and adj(a,b)),None)
 far=next((b for b in range(1,15) if not adj(0,b) and not any(adj(0,c) and adj(c,b) for c in range(15))),None)
 if tri:case=dict(kind='triangle',vertices=[0,*tri])
 elif far:case=dict(kind='distance_greater_than_two',vertices=[0,far])
 else:
  assert s in [41,70]
  assert all(adj(0,v)==adj(5,v)==adj(10,v) for v in range(15))
  case=dict(kind='three_twins',vertices=[0,5,10])
 out.append(dict(mask=s,jumps=sorted(S),**case))
(D/'outputs/order15-certificate.json').write_text(json.dumps(out,indent=2));print({k:sum(r['kind']==k for r in out) for k in {r['kind'] for r in out}})
