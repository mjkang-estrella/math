from pathlib import Path
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent; repo=B.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((lanes/'root-chatterjee-triangle-review-freeze-r1/review-freeze.json').read_text())
candidate=Path(freeze['source_lane']); review=lanes/'sol-chatterjee-triangle-preliminary-review-r1'
for name,h in freeze['files'].items():
    assert sha(candidate/name)==h
    assert sha(review/'frozen'/name)==h
review_files={str(p.relative_to(review)):sha(p) for p in sorted(review.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
(root/'review-hashes.json').write_text(json.dumps({'source_lane':str(review),'files':review_files},indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_files_verified':len(freeze['files']),'review_files_frozen':len(review_files),'math':'PASS: complete all-K construction, six literal population distances, joint density and positive distances','accepted_manuscript_scope':'PASS: full uniform multiplicative question for directed, average and max distances; not every possible Section 6 question','substantive':'PROVISIONAL PASS: no complete old compatible-triple bridge in inspected bodies; elementary construction objection retained','published_version':'HOLD: actual final body not compared','bounded_novelty':'HOLD: targeted trivariate copula antecedents and current semantic coverage incomplete','root_action':'Adopt scoped preliminary findings; targeted source/prior review next. No Lean or manuscript investment.','independent_review_checks':'102 exact directed values, 102 conditional-copy/CDF comparisons, 34 ratios, 17 densities; finite diagnostics separate from all-order proof','root_previous_checks':'78 directed values and 26 ratios; full ordinary proof read. No redundant replay required.','credit':0,'counts':{'additional':8,'total':38},'review_sha256':sha(review/'review.md')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md'; t=p.read_text(); t=t.replace('independent Chatterjee triangle review r1.','Chatterjee final-source/trivariate-prior review r2.')
t=t.replace('Routine modulo/shuffle adaptation, final-source comparison and informal approximate-scope attribution remain review gates.','Independent review confirms ordinary mathematics and full accepted-manuscript multiplicative scope, with provisional substantive PASS. Published-version comparison and targeted compatible-triple/copula prior-art clearance remain HOLD. Root adoption: root-chatterjee-preliminary-adoption-r1/ADOPTION.json.')
p.write_text(t)
paths=[p]
for folder in (root,review): paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt'; spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Adopt scoped Chatterjee review and preserve source and prior holds','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
