import json,pathlib,itertools
D=pathlib.Path(__file__).resolve().parents[1]
a=[202,225,232,149,232,22,23,31];b=[255^(1<<i)^a[i] for i in range(8)]
colors=[[0,1,2,2,3,0,3,1],[0,1,0,1,2,0,2,0]]
out=[]
for adj,c in zip([a,b],colors):
 cert=[]
 for x in range(8):
  for y in range(8):
   if x==y:cert.append([0,0]);continue
   found=None
   for sm in range(256):
    S={v for v in range(8) if sm>>v&1}
    if x in S or y in S or len({c[v] for v in S})!=len(S):continue
    if adj[x]>>y&1 and c[x] in {c[v] for v in S} and c[y] in {c[v] for v in S}:continue
    # Independent Floyd-Warshall implementation.
    r=[[i==j or (i not in S and j not in S and (adj[i]>>j&1) and {i,j}!={x,y}) for j in range(8)] for i in range(8)]
    for k in range(8):
     for i in range(8):
      for j in range(8):r[i][j]=r[i][j] or (r[i][k] and r[k][j])
    if not r[x][y]:
     am=sum(1<<v for v in range(8) if r[x][v])
     found=[sm,am];break
   assert found is not None,(x,y)
   cert.append(found)
 # Explicit length-7 reachability, enough for 8 vertices.
 reach=[1<<i for i in range(8)]
 for _ in range(7):
  reach=[z|sum(0 for _ in []) for z in reach]
  for i in range(8):
   old=reach[i]
   for j in range(8):
    if old>>j&1:reach[i]|=adj[j]
 assert reach==[255]*8
 out.append(dict(adjacency=adj,colors=c,certificates=cert))
(D/'outputs/rainbow-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
# Generate table definitions.
def vec(xs):return '!['+', '.join(map(str,xs))+']'
s=''
for idx,o in enumerate(out):
 s+=f'def color{idx} (v : Fin 8) : Fin {max(o["colors"])+1} := {vec(o["colors"])} v\n'
 s+=f'def cut{idx} (x y : Fin 8) (v : Fin 8) : Prop := ({vec([z[0] for z in o["certificates"]])} : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |>.testBit v.val = true\n'
 s+=f'def side{idx} (x y : Fin 8) (v : Fin 8) : Prop := ({vec([z[1] for z in o["certificates"]])} : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |>.testBit v.val = true\n'
 s+=f'instance (x y : Fin 8) (v : Fin 8) : Decidable (cut{idx} x y v) := inferInstanceAs (Decidable (_ = true))\n'
 s+=f'instance (x y : Fin 8) (v : Fin 8) : Decidable (side{idx} x y v) := inferInstanceAs (Decidable (_ = true))\n'
(D/'tables.txt').write_text(s)
print('independent Floyd check: all 112 ordered cuts verified; both graphs connected')
