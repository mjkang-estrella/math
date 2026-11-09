from pathlib import Path
import itertools,json,collections,re
P=Path(__file__).parent
words=[(0,5,10,1,6,11,2,7,12,3,8,13),(0,5,10,1,6,11,2,7,12,3,8,13,4,9),(0,5,10,1,6,11,2,7,12,3,8,13,4,9,14,5,10,0,6,11,1,7,12,2,8,13,3,9,14,4,10,0,5,11,1,6,12,2,7,13,3,8,14,4,9)]
# Bind explicit base word to the final C45 Appendix row in retained source extraction.
text=(P/'source.txt').read_text()
rows=re.findall(r'45\s+14\s+([0-9,\s]+)\.',text)
assert tuple(map(int,re.findall(r'\d+',rows[-1])))==words[2]
need={1:3,2:2,3:1,4:2,5:3,6:2,7:1,9:1,10:2,11:1,15:1}
assert list(map(len,words))==[12,14,45]
checks=0
for triple in itertools.product(range(3),repeat=3):
 w=sum((words[i] for i in triple),())
 for d,r in need.items():
  for i in range(len(w)-d):assert abs(w[i]-w[i+d])>=r,(triple,i,d);checks+=1
# Independent actual-graph BFS for C45 base; diagnostic for other finite orders.
def graph_check(w):
 n=len(w)
 for i in range(n):
  seen={i};layer={i}
  for d in range(1,4):
   layer={ (u+s)%n for u in layer for s in (-5,-1,1,5)}-seen;seen|=layer
   for j in layer:assert abs(w[i]-w[j])>=4-d,(n,i,j,d)
graph_check(words[2])
# For m=(n-45)/2 >=30 choose l in [0,5] congruent m mod6;
# then m-7l divisible by6, and nonnegative: only m=30..34 need checking.
for m in range(30,36):
 l=m%6;assert m-7*l>=0 and (m-7*l)%6==0
for n in range(105,501,2):
 m=(n-45)//2;l=m%6;k=(m-7*l)//6
 assert k>=0 and n==45+12*k+14*l
 graph_check(words[2]+words[0]*k+words[1]*l)
print(json.dumps(dict(words=[list(w) for w in words],all_27_ordered_triples_valid=True,integer_pair_checks=checks,C45_actual_graph_checked=True,coverage_residues=list(range(30,36)),actual_graph_diagnostics_odd_105_through_499=True)))
