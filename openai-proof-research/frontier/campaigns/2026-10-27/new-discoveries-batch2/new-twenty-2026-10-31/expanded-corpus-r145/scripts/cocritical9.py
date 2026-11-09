# n=9 step for MathDB 359361 (K3,K3): search all 9-vertex graphs with <=25 edges (< 4n-10=26) for
# co-critical ones. Every such G arises from an 8-vertex class H by adding a minimum-degree vertex of degree
# d<=5 with e(H)<=25-d. Filter: each non-edge needs >=2 common neighbours (necessary, see SUMMARY).
# Usage: cocritical9.py save | cocritical9.py run START END
import sys,json,itertools,time,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'scripts'))
import importlib.util
spec=importlib.util.spec_from_file_location('cc',str(D/'scripts/cocritical.py'))
src=(D/'scripts/cocritical.py').read_text().split('classes=[(0,)]')[0]
ns={}; exec(compile(src.replace('N=int(sys.argv[1])','N=0'),'cocritical_defs','exec'),ns)
canon,extend,good=ns['canon'],ns['extend'],ns['has_good_coloring']
f8=D/'outputs/graphs8.json'
if sys.argv[1]=='save':
    cl=[(0,)]
    for n in range(1,8): cl=extend(cl,n)
    f8.write_text(json.dumps([list(a) for a in cl])); print('saved',len(cl)); sys.exit()
a0,a1=int(sys.argv[2]),int(sys.argv[3]); EMAX=int(sys.argv[4]) if len(sys.argv)>4 else 25
H8=json.loads(f8.read_text()); t0=time.time()
cand=surv=0; found=[]
pc=[bin(x).count('1') for x in range(512)]
for idx in range(a0,min(a1,len(H8))):
    H=H8[idx]; eH=sum(pc[x] for x in H)//2
    degH=[pc[x] for x in H]
    for d in range(0,2*EMAX//9+1):
        if eH>EMAX-d: continue
        for S in itertools.combinations(range(8),d):
            cand+=1
            a=list(H)+[sum(1<<v for v in S)]
            for v in S: a[v]|=1<<8
            if min(pc[x] for x in a)<d: continue
            ok=True
            for v in range(9):
                nv=a[v]
                for u in range(v+1,9):
                    if not nv>>u&1 and pc[nv&a[u]]<2: ok=False;break
                if not ok: break
            if not ok: continue
            surv+=1
            if not good(9,a): continue
            if all(not good(9,[x|(1<<v) if i==u else (x|(1<<u) if i==v else x) for i,x in enumerate(a)]) for v in range(9) for u in range(v) if not a[v]>>u&1):
                found.append(a)
print(json.dumps(dict(range=[a0,min(a1,len(H8))],candidates=cand,survivors=surv,emax=EMAX,cocritical=len(found),edge_counts=sorted({sum(pc[x] for x in a)//2 for a in found}),examples=found[:5],sec=round(time.time()-t0,1))),flush=True)
