import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
# Exact reduced-graph template: red C5, blue complementary C5; green K_(2n) parts.
# A wheel contains a triangle. Both inter-part color graphs are triangle-free,
# and every green component has 2n vertices, fewer than the wheel's 2n+1.
out=[]
for n in range(2,13):
 size=2*n;N=5*size
 def col(i,j):
  a,b=i//size,j//size
  return 2 if a==b else 0 if (a-b)%5 in [1,4] else 1
 rainbow=any(len({col(a,b),col(a,c),col(b,c)})==3 for a,b,c in itertools.combinations(range(N),3))
 cross_triangle=any(len({a//size,b//size,c//size})>1 and col(a,b)==col(a,c)==col(b,c) for a,b,c in itertools.combinations(range(N),3))
 assert not rainbow and not cross_triangle
 out.append({'wheel_cycle':2*n,'colors':3,'vertices':N,'rainbow_triangle':rainbow,'cross_part_mono_triangle':cross_triangle,'green_component_size':size,'scope':'exact checked template; lower bound only, not a refutation; compare unknown R2 dependency'})
 print(out[-1],flush=True)
(D/'outputs/gallai.json').write_text(json.dumps(out,indent=2)+'\n')
