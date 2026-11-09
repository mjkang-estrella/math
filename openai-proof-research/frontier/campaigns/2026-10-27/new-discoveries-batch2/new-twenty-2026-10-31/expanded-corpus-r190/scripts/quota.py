import pathlib,json,itertools,collections
D=pathlib.Path(__file__).resolve().parents[1];es=list(itertools.product(range(3),range(3)));matches=[]
for m in range(512):
 ee=[es[j] for j in range(9) if m>>j&1]
 if len({a for a,b in ee})==len(ee)==len({b for a,b in ee}):matches.append(m)
worst=0;wit=None;cases=0
# Complete bipartite K_3,3 and every ordered pair of edge subsets.
for a in range(512):
 ca=(a.bit_count()+2)//3
 for b in range(512):
  cb=(b.bit_count()+2)//3;best=max(m.bit_count() for m in matches if (m&a).bit_count()<=ca and (m&b).bit_count()<=cb);gap=3-best;cases+=1
  if gap>worst:worst=gap;wit=[a,b,best]
o={'graph':'K3,3','edge_order':es,'m':2,'families':cases,'all_matchings':len(matches),'maximum_deficit':worst,'witness':wit,'limit':'Fixed m and order. Cannot refute existence of c(m), and does not prove a uniform c(m).'}
(D/'outputs/quota.json').write_text(json.dumps(o,indent=2));print(o)
