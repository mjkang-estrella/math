import json
r=json.loads(open('outputs/pmd-3-4.jsonl').readlines()[-1]);E=[tuple(e) for e in r['edges']]; layers=r['five_part'];g=(1<<len(E))-1;weights=[]
for b in layers:
 matching=[E[i] for i in range(len(E)) if b>>i&1]; used=set(sum((list(e) for e in matching),[]));order=[];todo=matching.copy()
 while todo:
  for u,v in todo:
   ds=lambda x:sum(1 for i,(a,c) in enumerate(E) if g>>i&1 and a in used and c in used and x in (a,c))
   if ds(u)==1:break
   if ds(v)==1:u,v=v,u;break
  else:raise Exception('no pendant')
  order.append((u,v));todo.remove(tuple(sorted((u,v))));used-={u,v}
 w=[None]*12
 for u,v in reversed(order):
  T=2+max([abs(x) for x in w if x is not None]+[0]);w[u]=T;w[v]=1-T
 T=2+max(abs(x) for x in w if x is not None)
 w=[-T if x is None else x for x in w]
 for i,(u,v) in enumerate(E):
  if g>>i&1:assert (w[u]+w[v]>0)==bool(b>>i&1),(i,w,b)
 weights.append(w);g^=b
assert g==0
out={'edges':E,'layers':[[E[i] for i in range(len(E)) if b>>i&1] for b in layers],'weights':weights,'verified_all_residual_edge_signs':True};json.dump(out,open('outputs/pmd-certificate.json','w'),indent=2);print(json.dumps(out))
