from pathlib import Path
from itertools import combinations
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];lane=lanes/'sol-fresh-source-discovery-r105'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
def occurrences(p):
    result=[]
    for idx in combinations(range(len(p)),4):
        a,b,c,d=(p[i] for i in idx)
        if not b<a<d<c: continue
        if all(not b<p[t]<c for t in range(idx[0]+1,idx[-1]) if t not in idx):result.append(idx)
    return result
def interleave(p,r):
    out=[]
    for i,v in enumerate(p):
        out.append(2*v-1)
        if i<len(r):out.append(2*r[i])
    return out
p=(2,1,4,3); r=(1,3,2);J=interleave(p,r)
assert occurrences(p)==[(0,1,2,3)]
assert (0,2,4,6) not in occurrences(J) and (0,1,3,5) in occurrences(J)
assert occurrences(interleave((2,3,1),(1,2)))
assert occurrences(interleave((1,2,3,5,4),(4,3,2,1)))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED / prior-attempt duplicate; zero nomination','credit':0,'counts':[8,38],'root_read':'Full SUMMARY/discovery and completed thread. Independently checked exact boxed2143 mixed-occurrence and monotone-completion failures.','root_exact_checks':{'J':J,'inherited_occurrence_destroyed':True,'mixed_occurrence_zero_based':[0,1,3,5],'increasing_and_decreasing_shortcuts_fail':True},'source_scope':'Kitaev-Qiu-Xu7.4 strict completion and7.5 factorial growth are unresolved related questions; Sudermann-Merx critical-triangle bound remains unresolved.','duplicate_correction':'Boxed12/Bruhat Conjecture8.5 was already attempted in embedded SCREENED-OUT-R71.md; identical insertion-state obstruction. Initial narrow screen missed it; expanded118618-file streaming audit caught it. No freshness or new contribution for8.5.','gap':['Uniform gap assignment forbidding inherited AND mixed boxed2143 occurrences or actual impossible input','Alternative factorial-growth construction if strict completion fails','Determinant-specific critical-constraint lower count despite nonlinear second-order rigidity'],'limits':'Generic one-active-constraint isolated optimum defeats only a counting shortcut, not the geometric source claim. Finite checks below source range do not establish new results.','manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md'),'holds':['Original2013 boxed-pattern body inaccessible','Current recursive registry tree403 and bounded semantic coverage'],'failures':'Wrong Omega main ref corrected to actualHEAD; guarded audit MemoryError retained and streaming rerun passed; initial vacuous checker corrected.','scope':'No PROOF.md, Lean, paper or credit. Preserve failures.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh finite/discrete discovery r105,','fresh finite/discrete discovery r108,');t=t.replace('Active Sol high/default:','r105 boxed2143 completion/growth and critical-triangle constraints remain unresolved. Expanded audit identifies boxed12 Conjecture8.5 as already attempted; initial freshness failure preserved. Root checked exact mixed-occurrence obstruction. See root-fresh-source-r105-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record boxed-pattern route gaps and corrected prior-attempt screen','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
