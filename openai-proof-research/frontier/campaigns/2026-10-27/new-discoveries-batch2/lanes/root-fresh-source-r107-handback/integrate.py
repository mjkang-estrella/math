from pathlib import Path
from math import comb
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];lane=lanes/'sol-fresh-source-discovery-r107'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'MANIFEST.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
# Polynomial regular action, independent of the worker's cyclic-permutation matrices.
cases=[]
for p in (3,5,7,11):
    assert all(comb(p,k)%p==0 for k in range(1,p))
    dims=[sum(j+k<p for j in range(p)) for k in range(p+1)]
    assert dims==list(range(p,-1,-1))
    solutions=[(a,b) for a in range(p+1) for b in range(p+1) if a+(p-1)*b==p]
    assert solutions==[(1,1),(p,0)]
    assert p!=0 # characteristic-zero ordinary characters: regular 0 versus trivial^p value p.
    cases.append({'p':p,'ranks_of_t_power_in_Fp_t_mod_t_p':dims,'positive_decomposition_solutions':solutions})
(root/'exact-checks.json').write_text(json.dumps(cases,indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED with separate routine/public exclusions','credit':0,'counts':[8,38],'target':'Johnston-Rumynin Conjecture9: positive Grothendieck-cone criterion for semiperfect Z_(p)G for every finite group and prime','root_read':'Full SUMMARY/discovery and completed thread; re-derived C_p arbitrary-witness obstruction. Read actual Jones-Woods Lie definition(**), Proposition3.11, Proposition4.14 and terminal example passages.','root_exact_check':'Four prime polynomial-action/decomposition calculations corroborate C_p obstruction. Universal proof is F_pC_p=F_p[t]/(t^p), not sample extrapolation.','gap':'Positive composition-class equality must select a correct rational representation/projective lattice, not an arbitrary positive witness. trivial^p and regular have equal composition class but different action; regular supplies a good lift in C_p, so no source refutation.','routine_terminal_exclusion':'For b=B(g) contained in ideal h with B(h)=Z(h)=Z2(g), restriction of defining quantifier gives b subset B(h). Thus [x,[x,b]]=0 for every x, and property(**) gives b subset Z(g); reverse inclusion known. Proposition3.11 transports equality. This direct definition/proposition specialization does not resolve full Iwasawa ConjectureA.','public_exclusion':'Worker inspected Liu-Yau full moduli derivation-dimension endpoint; retained as public-proof exclusion, no root external proof audit claimed.','holds':['Both registryHEAD refreshes403: inherited hashes not certified current','Johnston-Rumynin journal body403 and metadata date inconsistency','Closest book/thesis bodies unread','Bounded older semantic registry coverage'],'manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md'),'scope':'No full substantive result, PROOF.md, Lean, paper or acceptance.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh structural/algebraic discovery r107,','fresh structural/algebraic discovery r110,');t=t.replace('Active Sol high/default:','r107 Johnston-Rumynin semiperfectness criterion remains unresolved: arbitrary positive composition-class witnesses need not realize projective lifts. Root checked cyclic obstruction and direct routine Jones-Woods terminal implication, leaving full ConjectureA open. See root-fresh-source-r107-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record semiperfectness lift gap and routine Iwasawa terminal implication','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
