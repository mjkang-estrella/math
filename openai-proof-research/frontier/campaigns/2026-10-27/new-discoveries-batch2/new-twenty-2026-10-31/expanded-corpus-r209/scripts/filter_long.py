# keep graphs whose IR-graph path/cycle length >= threshold (recomputed), dedupe exact adjacency
import sys,json,importlib.util
inp,outp,thr=sys.argv[1],sys.argv[2],int(sys.argv[3])
gs=json.load(open(inp)); n=len(gs[0])
src=open(sys.argv[4]).read().split("t0=time.time(); keep")[0]
ns={'sys':sys}; src=src.replace("inp,outp,maxkeep,budget=sys.argv[1],sys.argv[2],int(sys.argv[3]),float(sys.argv[4])","").replace("graphs=json.load(open(inp)); n=len(graphs[0])+1","n=%d"%n)
exec(compile(src,'grow_head','exec'),ns)
out=[];seen=set();tally={}
for g in gs:
    if tuple(g) in seen: continue
    seen.add(tuple(g)); sh=ns['shape'](g)
    if sh and (sh[1]>=thr or sh[0]=='C'): out.append(g); tally[sh[0]+str(sh[1])]=tally.get(sh[0]+str(sh[1]),0)+1
json.dump(out,open(outp,'w')); print(len(out),tally)
