"""Exact finite controls; no universal proof or graph-isomorphism search."""
import json,collections
def mul(x,y,n):
 z=0
 for i in range(n):
  for j in range(n):
   b=0
   for k in range(n):b^=((x>>(i*n+k))&1)&((y>>(k*n+j))&1)
   z|=b<<(i*n+j)
 return z
tab=[[mul(a,b,2) for b in range(16)] for a in range(16)]
def block(x,y):
 a=x&1;b=(x>>1)&15;u=x>>5
 c=y&1;d=(y>>1)&15;v=y>>5
 return (a*c)|(tab[b][d]<<1)|(((v if a else 0)^tab[u][d])<<5)
def signature(product):
 sizes=[];center=[]
 for x in range(512):
  c=sum(product(x,y)==product(y,x) for y in range(512));sizes.append(c)
  if c==512:center.append(x)
 h=collections.Counter(c-len(center)-1 for x,c in enumerate(sizes) if x not in center)
 return dict(order=512,center=center,vertices=512-len(center),degree_histogram=dict(sorted(h.items())))
m=signature(lambda a,b:mul(a,b,3));r=signature(block)
assert len(m['center'])==len(r['center'])==2 and m['degree_histogram']!=r['degree_histogram']
# Square-zero ideal J consists of all (0,0,U). Associativity follows from the bimodule law;
# exhaustively check module action identity, not all 512^3 triples.
module_checks=0
for u in range(16):
 for b in range(16):
  for c in range(16):
   assert tab[tab[u][b]][c]==tab[u][tab[b][c]];module_checks+=1
for u in range(16):
 for v in range(16):assert block(u<<5,v<<5)==0
# Classical normalizer/radical-dimension bound arithmetic for conditional size transfer.
def vp(a,p):
 t=0
 while a%p==0:t+=1;a//=p
 return t
arithmetic=0
for p in [2,3,5,7]:
 for ell in [1,2,3]:
  for k in range(2,10):
   for n in range(2,10):
    upper=ell*k*k*n*(n-1)//2-vp(n,p)
    assert 2*upper<ell*(k*n)**2;arithmetic+=1
print(json.dumps(dict(matrix_M3_F2=m,triangular_bimodule_ring=r,square_zero_ideal_order=16,module_associativity_controls=module_checks,conditional_bound_controls=arithmetic,commutative_empty_graph_countermodel='F4 and F2[epsilon]/epsilon^2 have empty commuting graphs and order4 but only F4 is a field',scope='Finite exact diagnostics only; none settles the all-size conjecture'),indent=2,sort_keys=True))
