import json, hashlib, subprocess
from pathlib import Path
from datetime import datetime, timezone
import sympy as s

here=Path(__file__).resolve().parent
B=here.parents[1]; lanes=B/'lanes'; repo=B.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,obj): p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def verify(lane,manifest):
    d=json.loads(manifest.read_text())['files']
    for name,h in d.items(): assert sha(lane/name)==h,(lane,name)
    return len(d)
utc=datetime.now(timezone.utc).isoformat()
n89=verify(lanes/'sol-fresh-source-discovery-r89',lanes/'root-bajnok-beatty-review-freeze-r1/review-freeze.json')
n90=verify(lanes/'sol-fresh-source-discovery-r90',lanes/'root-mmpp-survival-review-freeze-r1/review-freeze.json')
n92=verify(lanes/'sol-fresh-source-discovery-r92',lanes/'sol-fresh-source-discovery-r92/manifest.json')

ex=lanes/'root-bajnok-beatty-exclusion-r1'
save(ex/'EXCLUSION.json',dict(utc=utc,decision='EXCLUDE_ROUTINE_SOURCE_ADAPTATION',credit=0,counts=[8,38],ordinary_math='PASS full published Conjecture1.6; source supplies sharp attainment.',root_inspection='Read complete preliminary review and actual cached VoR Theorems3.1 and3.2 proof passages, including equations3–6. Earlier root proof reading and693 exact residue cases retained.',bridge='Source already recovers both coefficient residues modulo an odd prime in Theorem3.1 and counts uniform coset fibers in Theorem3.2. Applying that counting to G/pG retains both residues; rotating the diamond gives dot products of alternating progression parity counts. The three minima and elementary quadratic comparison close the full bound; source constructors supply attainment.',countercase='Removes s-regularity and proves the complete sharp conjecture. This is a useful correct refinement; exclusion is a campaign boundary judgment about routine adaptation, not proof of an earlier published full endpoint. It is consistent with DeWitt/Defant exclusions.',novelty='HOLD separately; capped registry comparison and later classical-version coverage remain. No prior full proof asserted.',frozen_files_verified=n89,review='lanes/sol-bajnok-beatty-preliminary-review-r1/review.md',review_sha256=sha(lanes/'sol-bajnok-beatty-preliminary-review-r1/review.md'),scope='No Lean, paper or credit investment. Preserve proof and independent dissent/countercase.'))
ledger=json.loads((B/'ledger.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'])==(8,38)
entry=dict(id='bajnok-beatty-noncyclic-diameter',status='EXCLUDE_ROUTINE_SOURCE_ADAPTATION',discovery_count_credit=0,reason='Full correct proof is a two-coordinate refinement of source Theorems3.1–3.2 residue-fiber machinery and parity counts; source supplies all attainment. No previous printed full endpoint asserted.',decision='lanes/root-bajnok-beatty-exclusion-r1/EXCLUSION.json',novelty='HOLD independently')
assert isinstance(ledger['excluded'],list)
if not any(e.get('id')==entry['id'] for e in ledger['excluded']): ledger['excluded'].append(entry)
save(B/'ledger.json',ledger)

ad=lanes/'root-mmpp-preliminary-review-adoption-r1'
save(ad/'ADOPTION.json',dict(utc=utc,decision='ORDINARY_SOURCE_MATH_PASS_HISTORICAL_PRIORITY_HOLD',credit=0,counts=[8,38],frozen_files_verified=n90,review='lanes/sol-mmpp-survival-preliminary-review-r1/review.md',review_sha256=sha(lanes/'sol-mmpp-survival-preliminary-review-r1/review.md'),root='Read full independent review; earlier independent signed-row rational Taylor certificate remains valid. No redundant replay or formal claim.',source='Published Conjecture3.9 includes finite irreducible positive-rate cycle; Palm/time laws and embedded stationarity checked independently.',remaining='Actual Dan–Neuts1991 body, Asanjarani2017 thesis order proof, and possible classical cycle/Cox-to-finite-MMPP strict-crossing bridge need review. Indexed positive theorem or withdrawn abstract is not clearance.',next='New independent sol-mmpp-historical-prior-review-r2. No Lean or paper yet.',registry='Reviewer default Omega2130bf544f7858fc3c142bb9623b7ba9464e22ba,11commits4files from0292; OpenAI7ef5 unchanged. Bounded body/delta coverage, not worldwide priority.'))

x=s.symbols('x'); p=x**4+41*x**3+48*x**2+18*x+1
assert s.Poly(p,x).count_roots(-s.oo,0)==2
u=[0,1,3,3,1];v=[0,0,1,0,0]
mixed=2*u[3]*v[3]-u[2]*v[4]-v[2]*u[4]
assert mixed==-1
row=[0,1,250,4917,29648,75095,88704,43414,4861,1]
assert row[6]>row[5] and all(row[k]**2>=row[k-1]*row[k+1] for k in range(2,9))
r=lanes/'root-fresh-source-r92-handback'
save(r/'ADOPTION.json',dict(utc=utc,decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],manifest_files_verified=n92,root_checks={'quartic_negative_real_roots':2,'actual_component_mixed_term':mixed,'supplied_n10_vector_logconcave':True,'n10_mode_6_not_5':True},scope='Root read full discovery and summary. Limited independent exact checks verify only reported obstructions/vector facts, not RSK reconstruction or a full source theorem.',target='Sagan–Wilson full coefficient log-concavity, preprint6.3(c); published equivalence HOLD.',excluded='n10 mode defect already public at fengqiaoqu/plactic-peak-counterexample da399730a04f1044f72a413cee21a9319021cac1,2026-10-22, as body-read by worker. No new credit.',gap='Uniform exact weighted Ferrers-descent log-concavity; bounded n<=36 evidence does not close.',summary_sha256=sha(lanes/'sol-fresh-source-discovery-r92/SUMMARY.md')))

nextp=B/'NEXT.md'; text=nextp.read_text()
old=text.splitlines()
for i,line in enumerate(old):
    if line.startswith('r89 Bajnok'): old[i]='r89 Bajnok–Beatty full ordinary proof/source PASS, but root EXCLUDES campaign credit as routine source adaptation after independent review and actual VoR proof comparison. Current novelty HOLD remains separate. No Lean/paper. See root-bajnok-beatty-exclusion-r1/EXCLUSION.json.'
    if line.startswith('r90 supplies'): old[i]='r90 MMPP full ordinary counterexample now has independent source/math PASS and provisional substantive survival. Historical priority HOLD remains: Dan–Neuts1991 and Asanjarani2017 thesis bodies need reconciliation. Root signed-row certificate and55 frozen files verified. No Lean/paper/credit. See root-mmpp-preliminary-review-adoption-r1/ADOPTION.json.'
    if line.startswith('Active Sol high/default:'): old[i]='r92 plactic coefficient log-concavity remains unresolved; public n10 mode counterexample excluded. Root verified manifest and limited exact route obstructions; see root-fresh-source-r92-handback/ADOPTION.json.\nActive Sol high/default: MMPP historical-prior review r2, fresh finite/arithmetic r93, fresh analytic/probability r94. r74 sharp Chernoff curvature remains unresolved;'
nextp.write_text('\n'.join(old)+'\n')

git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
def commit(folders,files,title):
    paths=list(files)
    for folder in folders:
        paths.extend(p for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in ('.pyc','.olean','.ilean') and p.name!='commit-paths.txt')
    spec=here/'commit-paths.txt';spec.write_text('\n'.join(str(p.relative_to(repo)) for p in sorted(set(paths)))+'\n')
    subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
    subprocess.run(git+['commit','--quiet','-m',title,'--pathspec-from-file='+str(spec)],cwd=repo,check=True)
    subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
commit([ex,lanes/'sol-bajnok-beatty-preliminary-review-r1'],[B/'ledger.json'],'Exclude Bajnok Beatty proof as routine source adaptation')
commit([ad,lanes/'sol-mmpp-survival-preliminary-review-r1'],[],'Adopt MMPP mathematical review and retain historical priority hold')
commit([r,lanes/'sol-fresh-source-discovery-r92',here],[B/'NEXT.md'],'Preserve unresolved plactic log concavity and refresh research assignments')
print(json.dumps({'r89_freeze':n89,'r90_freeze':n90,'r92_manifest':n92,'counts':[8,38],'checks':'PASS'}))
