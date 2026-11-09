import pathlib,json,functools
L=pathlib.Path(__file__).resolve().parents[1];exec((L/'scripts/delta.py').read_text().split('out=[]')[0]);rng.seed(153)
G=random_cubic(18,1800);original=tuple(tuple(2*int(j in G[i]) for j in range(18)) for i in range(18))
seen=set();finals={}
def purepaths(T,path):
 if T in seen:return
 seen.add(T);A=list(map(list,T));W=wyes(A)
 if not W:finals[T]=path;return
 for x in W:purepaths(tuple(map(tuple,red(A,x))),path+[x])
purepaths(original,[]);minimum=min(map(len,finals));starts=sorted(T for T in finals if len(T)==minimum)
for T in starts:
 for rep in range(300):
  C=list(map(list,T));ops=[]
  for depth in range(12):
   ts=tris(C)
   if not ts:break
   t=rng.choice(ts);C=exp(C,t);ops.append(['expand',t])
   if rng.randrange(2) and (ts:=tris(C)):
    t=rng.choice(ts);C=exp(C,t);ops.append(['expand',t])
   while (W:=wyes(C)):
    x=rng.choice(W);C=red(C,x);ops.append(['reduce',x])
   if len(C)<minimum:
    out={'n':18,'original':original,'pure_reduction_graph_states':len(seen),'terminal_pure_states':len(finals),'minimum_pure_order':minimum,'minimum_pure_states':len(starts),'pure_reduction_sequence':finals[T],'Gprime':T,'operations':ops,'result':C,'Gprime_neighbor_counts':[sum(bool(x) for x in r) for r in T],'result_order':len(C)}
    (L/'outputs/delta-trace.json').write_text(json.dumps(out,indent=2));print('FOUND',minimum,len(C),'ops',len(ops),'neighbor counts',out['Gprime_neighbor_counts']);raise SystemExit
print('no trace found')
