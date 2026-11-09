# one-vertex extensions (all neighbourhoods) and single edge toggles+extensions of the 9-vertex hit graphs
import sys,json,importlib.util,itertools
L=sys.argv[1]; depth=int(sys.argv[2])
sys.argv=[sys.argv[0],'10','path','0','0']
s=importlib.util.spec_from_file_location('sa',L+'/scripts/ir_sa.py')
hits={}
for line in open(L+'/outputs/irgraph-N9-chunks.jsonl'):
    d=json.loads(line)
    for h in d['path_cycle_hits']: hits[tuple(h[0])]=h[1]
src=open(L+'/scripts/ir_sa.py').read().split('pairs=[(i,j)')[0]
ns={}; exec(compile(src.replace("n=int(sys.argv[1])","n=10").replace("target=sys.argv[2]","target='path'").replace("seed=int(sys.argv[3]); budget=float(sys.argv[4]);","seed=0;budget=0;"),'ir_sa_head','exec'),ns)
evaluate=ns['evaluate']
found={}
for g in hits:
    for nb in range(1<<9):
        adj=list(g)+[nb]
        for u in range(9):
            if nb>>u&1: adj[u]|=1<<9
        v,sh=ns['evaluate'](adj)
        if sh: found.setdefault(sh,adj)
print(json.dumps({'base_hits':len(hits),'shapes_found_10':{k:v for k,v in found.items()}}))
