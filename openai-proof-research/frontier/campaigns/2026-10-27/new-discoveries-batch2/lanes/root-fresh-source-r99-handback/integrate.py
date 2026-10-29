from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,itertools
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4];lane=root.parent/'sol-fresh-source-discovery-r99'
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,n=line.split(maxsplit=1);assert hashlib.sha256((lane/n.strip()).read_bytes()).hexdigest()==h,n;count+=1
horizontal={(i,i) for i in range(4)};vertical={(i,(i+1)%4) for i in range(4)}
assert not horizontal&vertical
assert all(sum(a==i for a,b in horizontal)==1 for i in range(4))
assert all(sum(b==j for a,b in vertical)==1 for j in range(4))
assert len(horizontal|vertical)==8 and 8>4+4-1
V=set(itertools.product(range(2),range(3)));D={(0,j) for j in range(3)};O=V-D
def adj(a,b):return (a[0]==b[0] and a[1]!=b[1]) or (a[1]==b[1] and a[0]!=b[0])
witness={}
for u in O:
    found=[v for v in D if {z for z in O if adj(v,z)}=={u}]
    assert found;witness[str(u)]=str(found[0])
assert not any(v[0]==1 for v in D)
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],manifest_files_verified=count,root_checks={'disjoint_budget_tokens':8,'conjectured_relaxed_upper':7,'K2_cartesian_K3_witnesses':witness,'empty_layer_not_super_dominating_in_K3':True},root_scope='Read full discovery and summary. Re-derived directional witness counting: each private edge changes one coordinate, yields row/column p bounds, loses product ab. Independently checked relaxation and literal layer obstructions. Did not repeat worker5.5million-subset census or certify full graph inequality.',target='Klein–Rodríguez-Velázquez–Yi published Conjecture2: gamma_sp(G square H)>=gamma_sp(G)*gamma_sp(H) for all finite simple graphs.',gap='Required outside bound nb+ma-ab; independent directional budgets yield only nb+ma. Eight-token relaxation is not graph-realized and not a source counterexample.',secondary='Kovács–Nagy forcing-density conjecture screened only; public code construction gives density-zero exceptions, no refutation.',source_prior='Worker actual VoR and matching-characterization bodies read; successor journal-version access gap and bounded registry coverage remain.',registry='9aef67a59dec08d1ff04a18a3d23560525ab023d; complete new3commit191file and1commit23file deltas, inherited older chain not root semantic audit.',summary_sha256=hashlib.sha256((lane/'SUMMARY.md').read_bytes()).hexdigest())
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
p=B/'NEXT.md';txt=p.read_text().replace('fresh graph/discrete optimization r99,','fresh graph/finite geometry r101,');txt=txt.replace('fresh arithmetic/algebraic r100,','fresh arithmetic/algebraic r100,');mark='independent Chatterjee triangle review r1.';txt=txt.replace(mark,mark+' r99 Cartesian super-domination remains unresolved; root checked both exact route obstructions and preserved missing ab coupling. See root-fresh-source-r99-handback/ADOPTION.json.');p.write_text(txt)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve super domination product gap and exact route obstructions','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'manifest_files':count,'root_checks':'PASS','counts':[8,38]}))
