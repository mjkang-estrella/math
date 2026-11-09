from trees import score,D
import networkx as nx,json
from fractions import Fraction
rows=[]
for n in range(4,101):
 target=Fraction(5*n-13+(n+1)*2**(n-4),2*n-5+2**(n-3))
 ds=[]
 for b in range(1,(n-2)//2+1):
  a=n-2-b
  val=2+Fraction(a*b*(2**(b-1)+2**(a-1)),1+a*2**b+b*2**a)
  ds.append((val,a,b))
 best,a,b=max(ds)
 assert best<=target
 rows.append({'n':n,'double_star_max':str(best),'R_n':str(target),'maximizing_parameters':[a,b]})
sp=[]
for n in range(5,61):
 for b in range(2,(n-1)//2+1):
  a=n-1-2*b;g=nx.Graph();g.add_node(0);v=1
  for _ in range(a):g.add_edge(0,v);v+=1
  for _ in range(b):g.add_edges_from([(0,v),(v,v+1)]);v+=2
  val=score(g);target=Fraction(5*n-13+(n+1)*2**(n-4),2*n-5+2**(n-3));assert val<=target
  sp.append({'n':n,'length1':a,'length2':b,'average':str(val),'gap':str(target-val)})
(D/'outputs/families.json').write_text(json.dumps({'double_stars':rows,'spiders':sp},indent=2)+'\n');print('Double stars n4..100 and',len(sp),'spiders n5..60: no violation.')
# Independent literal subset verification of the dynamic program on every tree through n9.
for n in range(2,10):
 for g in nx.nonisomorphic_trees(n):
  counts=[0,0]
  for mask in range(1<<n):
   if sum(bool(mask>>a&1) and bool(mask>>b&1) for a,b in g.edges())==1:counts[0]+=1;counts[1]+=mask.bit_count()
  assert score(g)==Fraction(counts[1],counts[0])
print('Independent subset checks passed through n9.')
