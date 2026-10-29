from pathlib import Path
import hashlib,json,subprocess
from datetime import datetime,timezone
root=Path(__file__).resolve().parent; B=root.parents[1];lanes=root.parent;repo=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
review=lanes/'sol-mmpp-classical-boundary-review-r3'
hashes=json.loads((review/'evidence-hashes.json').read_text())['files']
for n,h in hashes.items():assert sha(review/n)==h,n
frozen=json.loads((lanes/'root-mmpp-survival-review-freeze-r1/review-freeze.json').read_text())['files']
for n,h in frozen.items():assert sha(lanes/'sol-fresh-source-discovery-r90'/n)==h,n
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='SUBSTANTIVE_PASS_OVERALL_HISTORICAL_HOLD',credit=0,counts=[8,38],candidate_files_verified=len(frozen),review_artifacts_verified=len(hashes),review_sha256=sha(review/'review.md'),root_reading='Read full r3 adjudication. Prior root reading and independent symbolic/rational checks of r2 bridge retained; no redundant new formal or numerical replay claimed.',rationale='The located primary theorems provide Cox/Palm identities and stationarity. They do not provide this same-process oscillatory survival crossing. General MAP density does not license finite MMPP approximation; the explicit finite coupling supplies the required diagonal-D class and both normalized initial laws. The counterexample design and sign mechanism are source-specific constructive content, comparable to accepted short entropy/perspective and graph-gadget constructions. A newly derived elementary alternative is not automatically an existing routine corollary.',qualification='Routine unpublished specializations can still be excluded: absence of a printed exact endpoint alone is insufficient. Here no existing object-specific crossing construction or complete theorem specialization has been identified in the read bodies. All generic classical tools and finite certification receive zero separate credit.',dissent='Preserve sol-mmpp-historical-prior-review-r2 recommendation: a single harmonic and fast-cycle approximation may be nearly forced after the covariance formula. This is a contestable modest-end substantive boundary judgment. Root declines exclusion on the present evidence, not a claim of deep new machinery.',historical_holds=['Liu–Neuts1991 actual body','2026 Asanjarani–Hautphenne–Nazarathy moment-paper body','Newly surfaced Cox–Lewis sinusoidal-process body','AMS2024 stochastic-domination source scope','Relevant cookbook scope not established'],formal_status='No Lean or paper authorized; investment remains blocked by historical-priority coverage. No acceptance/count change.',next='Focused primary-body acquisition/comparison in sol-mmpp-primary-body-clearance-r4, not repeated eligibility opinions.',freshness='No new HEAD check by root in this turn; inherited dated small delta through d2b0ee6 and explicit truncated broader comparison retained.')
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
p=B/'NEXT.md';text=p.read_text();text=text.replace('MMPP classical-boundary adjudication r3,','MMPP primary-body clearance r4,')
text=text.replace('root retains HOLD pending distinction between a new elementary proof and published subsumption. See root-mmpp-boundary-hold-r3/ADJUDICATION-HOLD.json.','root now adopts substantive PASS after r3 adjudication, preserving r2 dissent. Historical body gaps still block Lean/paper and acceptance; see root-mmpp-substantive-adjudication-r4/ADOPTION.json. Earlier root-mmpp-boundary-hold-r3 remains historical.')
p.write_text(text)
paths=[p]
for folder in (root,review):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Adjudicate MMPP substantive eligibility and retain historical holds','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'candidate_hashes':len(frozen),'review_hashes':len(hashes),'status':'PASS','counts':[8,38]}))
