import datetime,hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent
B=P.parent.parent
S=P.parent/'sol-lasso-source-scope-review-r2'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
freeze=json.loads((P.parent/'root-lasso-review-freeze-r1/review-freeze.json').read_text())
for name,h in freeze['files'].items():
 assert sha(Path(freeze['source_lane'])/name)==h,name
 assert sha(S/'candidate-copy'/name)==h,name
manifest=json.loads((S/'ARTIFACT-HASHES.json').read_text())
for name,h in manifest.items():assert sha(S/name)==h,name
out={
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'decision':'EXCLUDE_CURRENT_NOMINATION; stop Lean and paper investment',
 'credit':0,'counts':[8,38],
 'review':'lanes/sol-lasso-source-scope-review-r2/review.md','review_sha256':sha(S/'review.md'),
 'ordinary_math':'PASS retained: relaxed SPD sign-averaged Gaussian criterion at p3,k2,beta1,c=-49999/100000,lambda1/20 exceeds61/250; orthogonal supremum is at most27/125.',
 'source_adjudication':'Root read actual cached target paragraph after Theorem3: summary discussion precedes a conjectural sentence qualified generally and written with fixed-lambda notation. No full universal optimized-domain quantifier is established. Complete journal VoR and closest dissertation/distinct SSD comparison remain unread. These are unresolved source gaps, not evidence of a false proof or a known duplicate.',
 'substantive_adjudication':'Source Lemma2 with p3,k2 and mixed signs makes inactive mean zero and variance (1-c)(1+2c)/(1+c) vanish at c down to -1/2 while active covariance stays nonsingular. Marginal bounds, Gaussian projection independence and Chebyshev give the explicit interior witness. The orthogonal maximum is bounded uniformly by a normal-density envelope and elementary cubic maximum. Root judges this completed specialization routine under campaign rules, independently reinforcing the attribution failure.',
 'countercase':'The optimized separation is stronger than plotted fixed-lambda failures and uses a different full-matrix boundary. It is not an identical printed theorem, and p3 alone is not the exclusion reason. Nevertheless the remaining uniform estimate is elementary once the source finite-dimensional distribution is specialized.',
 'scope_limits':['Not an exact balanced two-level or SSD design: such p3,V=I correlations require c>=-1/3.','No integral-summary, all-signal, or minimax-sign result.','Pointwise strict upper bounds imply supremum <=27/125, not a strict supremum bound.'],
 'novelty':'Selected actual bodies at dated complete18:13:38 registry heads contain no same-object result. This is bounded coverage, not worldwide absence; no exact earlier public proof is asserted.',
 'reopen_only_if':'Actual equation-faithful source context establishes an intended full optimized assertion, closest bodies are compared, and a substantive mechanism beyond the completed routine bridge is demonstrated.',
 'verification':{'frozen_original_and_copy_files':len(freeze['files']),'review_manifest_files':len(manifest),'all_hashes_match':True,'root_math_checks':'Earlier independent rational KKT/Schur/cubic checks retained; not redundantly rerun.','new_root_read':'Complete r2 review and actual target-section paragraph.'},
 'resource_qualification':'Reviewer helper_guard.py hash equals older runner without supervisor self-limits. Child caps are not an all-supervisor-compliance certificate. No heavy formal build occurred; root integrity integration uses improved self-limited guard.',
 'external_actions_performed':False}
(P/'EXCLUSION.json').write_text(json.dumps(out,indent=2)+'\n')
ledger=json.loads((B/'ledger.json').read_text())
assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
assert not any(e.get('id')=='lasso-optimized-sign-recovery' for e in ledger['excluded'])
ledger['excluded'].append({'id':'lasso-optimized-sign-recovery','status':'EXCLUDED_CURRENT_NOMINATION','credit':0,'reason':out['substantive_adjudication'],'source_scope':out['source_adjudication'],'decision':'lanes/root-lasso-exclusion-r2/EXCLUSION.json','review':out['review'],'ordinary_math':'PASS for relaxed SPD optimized separation; no exact public duplicate asserted.'})
(B/'ledger.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
n=(B/'NEXT.md').read_text()
start=n.index('r79 lasso yields')
end=n.index(' r74 sharp Chernoff',start)
n=n[:start]+('r79 lasso separation is ordinary-math sound but current nomination EXCLUDED: no clear attributable universal optimized quantifier, and completed source-Lemma2 boundary/cubic specialization is routine. VoR and closest-body gaps retained; no Lean or manuscript. See root-lasso-exclusion-r2/EXCLUSION.json.\nActive Sol high/default: fresh analysis/probability r81, finite/arithmetic r82, and structural/geometric r83.')+n[end:]
(B/'NEXT.md').write_text(n)
paths=[p for p in S.rglob('*') if p.is_file() and 'candidate-copy' not in p.parts and '__pycache__' not in p.parts]
paths.extend([P/'record.py',P/'EXCLUSION.json',P/'pathspec.txt',B/'ledger.json',B/'NEXT.md'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(B.parents[4]))+'\n' for p in sorted(paths)))
print(json.dumps({'decision':out['decision'],'frozen':len(freeze['files']),'review_files':len(manifest),'counts':[8,38]}))
