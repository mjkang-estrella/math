import pathlib,sys,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);mask=int(sys.argv[2]);ell=int(sys.argv[3]);idx=int(sys.argv[4]);sys.argv=[sys.argv[0],str(n),'1']
# load definitions without the search loop
src=(D/'scripts/cover.py').read_text().split('for mask in range(')[0];exec(src)
E=base+[e for j,e in enumerate(opts) if mask>>j&1]
names=[f'{t}{i}' for i in range(n,0,-1) for t in ['x','y']]
cs=[]
for c in range(1<<2*n):
 if c.bit_count()==n and all(c>>a&1 or c>>b&1 for a,b in E):cs.append(tuple(c>>v&1 for v in range(2*n)))
gs={(0,)*2*n}
for _ in range(ell):gs={tuple(a+b for a,b in zip(g,h)) for g in gs for h in cs}
ordered=sorted(gs,reverse=True);C,k=cols(ordered);hs=set()
for g,co in zip(ordered,C):
 for s in itertools.combinations(co,idx):hs.add(tuple(a+(v in s) for v,a in enumerate(g)))
hs=sorted(hs,reverse=True);cc,k=cols(hs)
def mono(g):return '*'.join(names[i]+('^'+str(e) if e>1 else '') for i,e in enumerate(g) if e)
r={'graph':[[names[a],names[b]] for a,b in E],'generators':[mono(g) for g in ordered],'colon_sets':[[names[t] for t in c] for c in C],'shift_generators':[mono(g) for g in hs],'failure_index':k,'failed_colon':[mono(tuple(max(0,a-b) for a,b in zip(h,hs[k]))) for h in hs[:k]]}
print(json.dumps(r,indent=2));(D/f'outputs/cover-detail-{n}-{mask}-{ell}-{idx}.json').write_text(json.dumps(r,indent=2))
