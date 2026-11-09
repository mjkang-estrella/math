exec(open(__file__.replace('leaf_extended.py','leaf_search.py')).read().split('results=[]')[0])
out=[]
for lengths in [(4,2,2,2),(4,4,2,2)]:
 es=[(0,1)];v=2;color={0:0,1:1}
 for root,l in zip([0,0,1,1],lengths):
  prev=root
  for _ in range(l):es.append((prev,v));color[v]=1-color[prev];prev=v;v+=1
 # adapt analyze to actual vertex number while preserving exact matching semantics
 import inspect
 code=open(__file__.replace('leaf_extended.py','leaf_search.py')).read();code=code[code.index('def analyze'):code.index('results=[]')].replace('[0]*10','[0]*'+str(v)).replace('range(10)','range('+str(v)+')');exec(code)
 ex=[(a,b) for a in range(v) for b in range(a+1,v) if color[a]!=color[b] and (a,b) not in es];cnt=0;surv=0
 for xs in [()]+[(x,) for x in ex]:
  cnt+=1;res=analyze(es+list(xs))
  if res:
   surv+=1
   if 'bad_vertices' in res:print('FOUND',res,flush=True);(p/'leaf-extended-witness.json').write_text(json.dumps(res,indent=2));raise SystemExit
 out.append({'arm_lengths':lengths,'vertices':v,'graphs':cnt,'ratio_lt_one':surv});print(out[-1],flush=True)
(p/'leaf-extended-diagnostic.json').write_text(json.dumps(out,indent=2))
