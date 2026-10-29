import datetime, hashlib, json
from pathlib import Path
P=Path(__file__).resolve().parent
B=P.parent.parent
cwd=B.parents[4]
review=P.parent/'sol-silicosis-multiplicity-preliminary-review-r1'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return h.hexdigest()
freeze=json.loads((P.parent/'root-silicosis-review-freeze-r1/review-freeze.json').read_text())
src=Path(freeze['source_lane'])
for n,h in freeze['files'].items():
    assert sha(src/n)==h and sha(review/'frozen'/n)==h,n
manifest=json.loads((review/'evidence-manifest.json').read_text())['files']
for n,h in manifest.items():assert sha(review/n)==h,n
record={
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'decision':'EXCLUDE_ROUTINE; stop formal and manuscript investment',
 'credit':0,'counts':[7,37],
 'review':'lanes/sol-silicosis-multiplicity-preliminary-review-r1/review.md',
 'review_sha256':sha(review/'review.md'),
 'ordinary_math':'PASS for surviving all-power-law multiplicity and exact level ranges',
 'source':'Relevant published correspondence PASS; VoR obtained by reviewer. Root read actual extracted Corollary7 and Section5, including existence/uniqueness distinction. No root visual-page audit claimed.',
 'publication_correction':'Revised23September2019; accepted11October2019, first online31October2019. September manuscript is not final acceptance date.',
 'vor_sha256':sha(review/'vor.pdf'),
 'root_classical_body_read':'Hirschman1964 actual extracted Definition2a/Theorem2b p100 and pointwise-limit principle(i) p101. Total nonnegativity implies variation diminution, zeros allowed.',
 'complete_bridge':'Clearing denominators of the nested positive-product basis gives A_N=L_N diag(A_(N-1),1). Positive lower bidiagonal L_N is totally nonnegative by ordered-minor matching, and Cauchy-Binet preserves this under products. Classical variation diminution and Descartes bound roots by the level coefficient sign changes. The source telescope and elementary derivative of i/(1+i^(a-b)) give at most two changes. Normal convergence and finite alternating-sign limits give quasiconcavity; analyticity and endpoints give strict unimodality and exact multiplicity. No remaining parameter inequality or comparison theorem is assumed.',
 'countercase':'Source leaves intended multiplicity open and its suggested curvature route is bypassed. This can be useful new-to-literature exposition; no exact prior silicosis theorem is asserted. Root nevertheless judges the fully discharged generic transform application routine under campaign rules.',
 'not_claimed':['H second-derivative sign','K curvature','dynamical stability','full Lean endpoint','worldwide priority'],
 'scope_correction':'Physical exponents give b<=a. At b=a-1 the actual range is (0,1); literal existence for every positive level is false, but that wording correction is not credited or the reason for excluding intended multiplicity.',
 'bounded_novelty':'No exact earlier full theorem located; saved complete registry observations dated17:20UTC remain bounded evidence, not current forever.',
 'verification':{'frozen_original_and_copy_files':len(freeze['files']),'review_manifest_files':len(manifest),'all_hashes_match':True,'root_earlier_exact_checks':4665,'reviewer_checks_not_root_replayed':True},
 'review_evidence_manifest_sha256':sha(review/'evidence-manifest.json')
}
(P/'EXCLUSION.json').write_text(json.dumps(record,indent=2)+'\n')
nf=B/'NEXT.md';t=nf.read_text()
t=t.replace('r76 supplies a complete ordinary silicosis multiplicity candidate, with\nclassical-subsumption/source-scope holds; independent review pending, credit0.', 'r76 silicosis full intended multiplicity is ordinary-math sound but EXCLUDED\nas a routine classical variation-diminishing/Descartes reduction. Published VoR\ncomparison now passes; equality existence qualification retained. Root decision:\nroot-silicosis-exclusion-r1/EXCLUSION.json. No Lean or manuscript investment.')
t=t.replace('formal r2, and silicosis preliminary review r1.', 'formal r2, and fresh source discovery r78.')
nf.write_text(t)
lf=B/'ledger.json';ledger=json.loads(lf.read_text())
entry={'id':'silicosis-power-law-multiplicity','status':'EXCLUDED_ROUTINE','credit':0,'reason':record['complete_bridge'],'decision':'lanes/root-silicosis-exclusion-r1/EXCLUSION.json','review':record['review'],'scope_note':'Ordinary full intended multiplicity PASS; published correspondence PASS with equality existence qualification. No earlier exact printed duplicate asserted; no formal endpoint.'}
if not any(e.get('id')==entry['id'] for e in ledger['excluded']):ledger['excluded'].append(entry)
lf.write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
paths=[]
for folder in (review,P):
    paths.extend(str(f.relative_to(cwd)) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt')
paths += [str(f.relative_to(cwd)) for f in (nf,lf)]
(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'decision':record['decision'],'freeze':len(freeze['files']),'review_manifest':len(manifest),'hashes':'PASS','counts':[7,37]}))
