from pathlib import Path
from itertools import combinations
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];lane=lanes/'sol-fresh-source-discovery-r102'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
# Independently check the small classification obstruction and explicit multipartite witnesses.
edges=set(combinations(range(6),2)); minima=0
for missing in combinations(edges,2):
    g=edges-set(missing); assert len(g)==13
    assert all(len(g|{e})==14 for e in missing);minima+=1
assert minima==105
g=edges-{(0,1),(2,3)}
assert sum(sum(v in e for e in g)==5 for v in range(6))==2
witnesses=0
for s,k in ((2,3),(3,5),(4,7),(6,8)):
    t=(k+1)//2; vertices=list(range((s+1)*t)); part=lambda v:v//t
    E={e for e in combinations(vertices,2) if part(e[0])!=part(e[1])}
    for p in range(s+1):
        xy=(p*t,p*t+1); assert xy not in E
        other=[q for q in range(s+1) if q!=p]
        centers=[*xy]+[q*t for q in other[:s-2]]
        a,b=other[-2:];path=[(a if i%2==0 else b)*t+i//2 for i in range(k)]
        augmented=E|{xy};pair=lambda a,b:tuple(sorted((a,b)))
        assert len(set(centers+path))==s+k
        assert all(pair(a,b) in augmented for a,b in combinations(centers,2))
        assert all(pair(a,b) in augmented for a in centers for b in path)
        assert all(pair(a,b) in augmented for a,b in zip(path,path[1:]))
        witnesses+=1
# Exact edge partition algebra, independent of saturation assumptions.
checks=0
for s in range(2,8):
    for d in range(s,2*s+3):
        n=d+7; ea=s*(s-1)//2+2;excess=3;eb=4;r=d-s
        C=ea-s*(s-1)//2+excess+eb
        assert d+ea+s*(n-d-1)+excess+eb==s*n-s*(s+1)//2-(s-1)*r+C
        checks+=1
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; no discovery nomination','credit':0,'counts':[8,38],'source':'Li-You-Zhang2610.34990v1 Conjecture1.1 all-s clique-path saturation and Section4 minimum-graph classification; s=3 number already proved in source','root_read':'Full SUMMARY/discovery and completed thread; re-derived cone swap, common-clique witness and edge partition. No independent full source/prior clearance asserted.','root_exact_checks':{'six_vertex_13_edge_minima':minima,'universal_vertices_in_K6_minus_disjoint_edges':2,'multipartite_missing_edge_witnesses':witnesses,'charge_identity_checks':checks},'limits':'Explicit obstruction checks only. No uniform lower bound or extremizer classification. K_s join independent is not saturated; nonuniversal multipartite examples are saturated but not numerical counterexamples.','gap':'For nonuniversal saturated hosts with s+1<=delta<=2s+1 prove C >= (s-1)(delta-s)+sat(n-s,P_k); classification also remains open.','source_prior_holds':['Original s=2 journal body403','Original1986 path-saturation proof unread','Bounded inherited registry semantic coverage'],'protocol':'Worker disclosed one trivial unguarded parser-edit helper; not erased or called compliant. Heavy checks were capped.','manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh finite/arithmetic discovery r102,','fresh finite/discrete discovery r105,');t=t.replace('Active Sol high/default:','r102 clique-path saturation and minimum-graph classification remain unresolved. Root checked the exact charging identity and explicit multipartite/minimum-graph route obstructions; original-body and semantic coverage holds retained. See root-fresh-source-r102-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record unresolved clique-path saturation and exact route obstructions','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
