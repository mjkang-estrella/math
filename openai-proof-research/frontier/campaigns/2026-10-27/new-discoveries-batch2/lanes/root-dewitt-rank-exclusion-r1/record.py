import datetime,hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;S=P.parent/'sol-dewitt-rank-preliminary-review-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
f=json.loads((P.parent/'root-dewitt-rank-review-freeze-r1/review-freeze.json').read_text())
for name,h in f['files'].items():
 assert sha(Path(f['source_lane'])/name)==h,name
 assert sha(S/'frozen'/name)==h,name
pr=json.loads((S/'provenance.json').read_text())
for name,d in pr['all_artifacts'].items():assert sha(S/name)==d['sha256'],name
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'EXCLUDE_ROUTINE_SOURCE_ADAPTATION','credit':0,'counts':[8,38],
 'ordinary_math':'PASS for the full numbered preprint Conjecture1 using explicitly known unrefined total congruences. Subsequent residue-zero prose is not proved.',
 'root_inspection':'Root read complete candidate proof, discovery and independent review, then actual cached source Lemma8, Lemma9 with proofs and Section5 conjecture context. Earlier independent small exact counts retained.',
 'complete_bridge':'The source supplies nine parity classes and conjugation, the partial-doubling reduction E_s≡2|S|mod4, the same conjugate/reversal/conjugate involution and both fixed types, and Lemma9 exact E_r−E_s=σ1(m)−d(m). Keeping crossed fixed pairs instead of excluding them gives d(m)/2 when m≡1mod4. Elementary prime valuation and nonsquare residue facts give d(m),σ1(m)≡0mod4 on the other four progressions; known total counts supply odd parity by subtraction. No new involution, classification, or unresolved uniform estimate remains.',
 'countercase':'The source explicitly conjectures the rank endpoint and says its main proof does not immediately generalize. The candidate is a useful valid refinement, but imports the established total congruences and counts an exceptional family already classified in the source. Root excludes the routine adaptation, not merely a short proof; no previously printed identical endpoint asserted.',
 'source_hold':'Actual journal Section5 and definitions unread. First-page preview revision27Oct2025/acceptance9Dec2025 postdate arXivv1. Metadata or first page do not establish journal equivalence.',
 'novelty_hold':'Current-registry semantic clearance incomplete; negative search does not prove priority. Exclusion does not turn that HOLD into a prior-proof claim.',
 'scope':'No Lean or paper investment; no residue-zero refinement, entirely new combinatorial proof of unrefined totals, or separate helper credit.',
 'review':'lanes/sol-dewitt-rank-preliminary-review-r1/review.md','review_sha256':sha(S/'review.md'),
 'proof_sha256':sha(Path(f['source_lane'])/'PROOF.md'),'frozen_original_and_copy_files':len(f['files']),'review_artifacts_verified':len(pr['all_artifacts']),
 'validation':'Root29boundedchecks previously passed. Reviewer independent area-factor enumeration and exact map checks PASS; root did not redundantly replay them.',
 'external_actions_performed':False}
(P/'EXCLUSION.json').write_text(json.dumps(out,indent=2)+'\n')
ledger=json.loads((B/'ledger.json').read_text());assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
key='dewitt-keith-two-size-rank-parity'
assert not any(x.get('id')==key for x in ledger['excluded'])
ledger['excluded'].append({'id':key,'status':out['decision'],'credit':0,'reason':out['complete_bridge'],'scope_note':out['ordinary_math'],'source_hold':out['source_hold'],'decision':'lanes/root-dewitt-rank-exclusion-r1/EXCLUSION.json','review':out['review']})
(B/'ledger.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
n=(B/'NEXT.md').read_text()
old='r82 supplies a full ordinary parity-rank proof of DeWitt–Keith numbered Conjecture1 using known total congruences; root29boundedchecks agree. Routine source-involution adaptation, stronger residue-zero prose scope, journal comparison and current prior clearance require independent review. Frozen29files in root-dewitt-rank-review-freeze-r1; credit0, no Lean/paper.'
assert old in n
n=n.replace(old,'r82 DeWitt–Keith full numbered parity-rank proof is ordinary-math PASS but EXCLUDED as routine source adaptation after independent review and root actual Lemma8/9 reading. Residue-zero prose unproved; journal/current-prior holds retained. See root-dewitt-rank-exclusion-r1/EXCLUSION.json. No Lean or paper.')
n=n.replace('DeWitt–Keith rank preliminary review r1,','fresh finite/arithmetic r87,')
(B/'NEXT.md').write_text(n)
paths=[p for p in S.rglob('*') if p.is_file() and 'frozen' not in p.parts and '__pycache__' not in p.parts]
paths.extend([P/'record.py',P/'EXCLUSION.json',P/'pathspec.txt',B/'ledger.json',B/'NEXT.md'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(B.parents[4]))+'\n' for p in sorted(paths)))
print(json.dumps({'decision':out['decision'],'frozen':len(f['files']),'review_artifacts':len(pr['all_artifacts']),'counts':[8,38]}))
