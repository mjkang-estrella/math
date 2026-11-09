import importlib.util,json
spec=importlib.util.spec_from_file_location('ind','scripts/independent.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
a=[202,225,232,149,232,22,23,31];res=[]
for graph in [a,m.comp(a)]:
 cs=m.cuts(graph);c=[0]*8;hist={};examples={}
 def visit(i,mx):
  if i==8:
   k=max(c)+1;ok=m.valid(c,cs);h=hist.setdefault(k,{'total':0,'valid':0});h['total']+=1;h['valid']+=ok
   if ok:examples.setdefault(k,c.copy())
   return
  for col in range(mx+2):c[i]=col;visit(i+1,max(mx,col))
 visit(1,0)
 assert sum(v['total'] for v in hist.values())==4140
 res.append({'all_4140_partitions':hist,'minimum':min(examples),'examples':examples})
open('brute-candidate.json','w').write(json.dumps(res,indent=2));print(json.dumps(res))
