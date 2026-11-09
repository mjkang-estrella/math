import pathlib,runpy,itertools,json,time,random
D=pathlib.Path(__file__).resolve().parents[1]
# Load definitions without running phase 1
s=(D/'scripts/dag.py').read_text().split('rng=random.Random')[0];ns={'__file__':str(D/'scripts/dag.py')};exec(compile(s,str(D/'scripts/dag.py'),'exec'),ns);feasible=ns['feasible'];closure=ns['closure']
t=time.monotonic();out={'space':'all 4 by 4 bipartite forward-edge subsets with weak connectivity','graphs':0,'feasible':0,'limited':0}
for mask in range(1<<16):
 e=[(i,4+j) for i in range(4) for j in range(4) if mask>>(4*i+j)&1];seen={0}
 while True:
  nxt=seen|{b for a,b in e if a in seen}|{a for a,b in e if b in seen}
  if nxt==seen:break
  seen=nxt
 if len(seen)!=8:continue
 out['graphs']+=1;r,c,l=feasible(closure(8,e))
 if r is not None:out['feasible']+=1
 elif l:out['limited']+=1
 else:out['potential_failure']=e;break
out['seconds']=time.monotonic()-t;print(out,flush=True);(D/'outputs/dag2.json').write_text(json.dumps(out,indent=2))
