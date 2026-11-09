import pathlib,json,hashlib,itertools
L=pathlib.Path(__file__).parent
F=[(0,1),(0,5),(1,2),(1,6),(2,7),(3,5),(3,6),(4,6),(4,7),(5,7)];FE=[0,2,3,4]
C=[(0,1),(0,2),(0,3)];CE=[3,1,1,2,2,3]
lj=[((0,0),(3,2)),((0,2),(4,0)),((0,3),(4,1)),((1,1),(4,2)),((1,0),(4,3)),((2,0),(4,4)),((3,0),(4,5)),((1,2),(2,1)),((2,2),(3,1))]
gj=[((0,0),(2,2)),((0,1),(1,1)),((0,2),(3,0)),((0,3),(3,1)),((1,0),(3,2)),((1,2),(3,4)),((2,1),(3,3)),((2,0),(3,5)),((1,3),(2,3))]
def leaf(es,ps,n,colors):return ([(a,b,c) for (a,b),c in zip(es,colors)],[(v,colors[len(es)+i]) for i,v in enumerate(ps)],n)
def join(parts,joins,remaining):
 es=[];ps=[];off=0
 for ee,pp,n in parts:
  es.extend((a+off,b+off,c) for a,b,c in ee);ps.append([(v+off,c) for v,c in pp]);off+=n
 for (a,i),(b,j) in joins:
  u,c=ps[a][i];v,d=ps[b][j];assert c==d;es.append((u,v,c))
 return es,[ps[a][i] for a,i in remaining],off
t=json.loads((L/'L-table.json').read_text());r=json.loads((L/'G-result.json').read_text());w=r['witness'];assert w
parts=[]
for v in w['L_witnesses']:
 i=(v&((1<<24)-1))>>7;pi=v&127;p=list(itertools.permutations(range(5)))[pi]
 ch=t['rows'][i]['children'];q=join([leaf(F,FE,8,c) for c in ch[:4]]+[leaf(C,CE,4,ch[4])],lj,[(0,1),(1,3),(2,3),(3,3)])
 parts.append(([(a,b,p[c]) for a,b,c in q[0]],[(v,p[c]) for v,c in q[1]],q[2]))
parts.append(leaf(C,CE,4,w['claw']['colors']))
es,ps,n=join(parts,gj,[]);assert n==112 and not ps
edges=sorted((min(a,b),max(a,b),c) for a,b,c in es)
stars=[set() for _ in range(n)]
for a,b,c in edges:stars[a].add(c);stars[b].add(c)
assert all(len(s)==3 for s in stars)
bad=[(a,b) for a,b,c in edges if len(stars[a]|stars[b])==4];assert len(bad)==2
def perm(x):
 for lo,hi,k in [(0,7,0),(8,31,4),(32,35,-24),(36,43,4),(44,67,8),(68,71,-20),(72,79,4),(80,103,8),(104,107,-20),(108,111,-72)]:
  if lo<=x<=hi:return x+k
ref=sorted(sorted((perm(a),perm(b))) for a,b,c in edges)
sha=hashlib.sha256(json.dumps(ref,separators=(',',':')).encode()).hexdigest();assert sha=='dc16cc18600cf77c8661b7baf89c7019f265299308541961ff884ea7187b4e8b'
out={'edges_colors':edges,'abnormal_edges':bad,'palettes':[sorted(s) for s in stars],'normalized_reference_sha256':sha,'claim':'explicit proper five-edge-coloring with exactly two abnormal edges; non-normal-colorability relies on Putman Theorem1.1, not local DRAT replay'}
(L/'two-defect-witness.json').write_text(json.dumps(out,indent=2));print({'abnormal_edges':bad,'sha256':sha})
