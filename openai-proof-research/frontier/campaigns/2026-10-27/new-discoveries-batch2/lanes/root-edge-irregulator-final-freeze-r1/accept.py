import datetime, hashlib, json, shutil
from pathlib import Path

P = Path(__file__).resolve().parent
B = P.parent.parent
ROOT = B.parents[4]
S = P.parent / 'sol-edge-irregulator-manuscript-packet-r1'
F = P.parent / 'sol-edge-irregulator-full-final-review-r1'
A = P.parent / 'root-edge-irregulator-acceptance-r1'
C = B / 'candidates/edge-irregulator'
L = P.parent / 'root-lasso-review-adoption-r1'
for p in (A, C, L): p.mkdir(exist_ok=True)

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()

def dump(p, value): p.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
freeze = json.loads((P/'review-freeze.json').read_text())
assert len(freeze['files']) == 145
for name, h in freeze['files'].items(): assert sha(S/name) == h, name
lf = json.loads((P.parent/'root-lasso-review-freeze-r1/review-freeze.json').read_text())
for name, h in lf['files'].items(): assert sha(Path(lf['source_lane'])/name) == h, name
v = json.loads((P/'extracted/verification-receipt.json').read_text())
assert v['declaration_count'] == 167 and len(v['proof_modules']) == 14
assert v['pdf_byte_identical'] and v['zip_byte_identical']
assert v['all_unsafe_partial_axiom_flags_false']
assert set(v['axiom_union']) == {'propext','Classical.choice','Quot.sound'}
archive = S/'edge-irregulator-manuscript-packet.zip'
assert sha(archive) == 'eec110ef7c3d49062da7dd211fca39227e2841ef9ec311921f463e197f4d6813'
assert sha(P/'extracted/rebuilt.zip') == sha(archive)
first = B.parent.parent/'2026-10-26/new-discoveries/ledger.json'
first_hash = '4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385'
assert sha(first) == first_hash
for name in ('verification-receipt.json','replay-receipt.json','audit-inventory.json'):
    shutil.copy2(P/'extracted'/name, A/name)
shutil.copytree(P/'extracted/logs', A/'logs', dirs_exist_ok=True)
shutil.copy2(archive, B/'candidate-packets/connected-edge-irregulator-refutation.zip')
for name in ('paper.pdf','paper.tex'):
    shutil.copy2(S/'packet'/name, C/name)

entry = {
 'number':38, 'status':'ACCEPT: full published connected-graph conjecture refuted; root and independent final extracted replay PASS; bounded prior-art limits retained',
 'discovery_count_credit':1, 'title':'Unbounded excess over the one-third edge-irregulator bound',
 'source_target':'Bensmail–Catherinot–Fioravantes–Marcille–Oijid, Graph Irregularity via Edge Deletions, WALCOM 2026, Conjecture 1, printed p356',
 'source_url':'https://doi.org/10.1007/978-981-95-7127-7_24',
 'scope':'For every integer t>=2, a connected simple graph with 6t+1 vertices and 8t edges has exact edge-irregulator minimum 3t. Hence no real absolute c>=1 satisfies I_e(G)<=|E(G)|/3+c for every connected finite simple graph.',
 'formal_modules':14, 'formal_declarations':167,
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'all_actual_unsafe_partial_axiom_flags_false':True,
 'endpoint':'EdgeIrregulator.main', 'source_refutation':'EdgeIrregulator.source_refutation : ¬ EdgeIrregulator.SourceClaim',
 'packet':'candidate-packets/connected-edge-irregulator-refutation.zip', 'packet_sha256':sha(archive),
 'paper':'candidates/edge-irregulator/paper.pdf', 'paper_sha256':sha(C/'paper.pdf'),
 'manifest_sha256':sha(S/'packet/manifest.json'),
 'receipt_sha256':sha(A/'verification-receipt.json'),
 'final_extracted_receipt':'lanes/root-edge-irregulator-acceptance-r1/verification-receipt.json',
 'parent_decision':'lanes/root-edge-irregulator-acceptance-r1/ACCEPTANCE.json',
 'independent_reviews':['lanes/sol-edge-irregulator-preliminary-review-r1/review.md','lanes/sol-edge-irregulator-current-prior-review-r2/review.md','lanes/sol-edge-irregulator-full-final-review-r1/review.md'],
 'substantive_adjudication':'Full intended unbounded-family refutation. The boundary-independent diamond cost adds two deletions to a three-edge path cost; actual disjoint charges preserve connectedness and force density 3/8. Inspected subdivision theorem supplies only 1/3; hardness gadgets and positive-label results supply no density-preserving bridge. Small-gadget shortness is not credited as a tool, but no complete classical subsumption was demonstrated.',
 'novelty_limit':'Dated complete registry inventories and selected actual primary bodies at 2026-10-29T18:13:38Z; final reviewer checked 222-path Omega delta and relevant actual statements. No matching prior proof or complete subsumer found within this scope. Broader decomposition literature not exhaustively read; no worldwide priority guarantee.',
 'registry_evidence':'lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',
 'one_family':'One full source refutation; exact minimum, local boundary lemma, upper witness and all helpers receive no separate credit.',
 'resource_limit':'Final replay used capped helpers and serial capped Lean. RSS observations are sampled, not absolute peaks. Earlier lower receipt overwrite, upper helper supervision omission and packet supervisor self-limit deviation remain preserved in historical evidence.',
 'postreview_manuscript_change':'None. Exact reviewed four-page PDF and source ZIP retained byte-identically, including historical pending-review/credit-zero text. This dated acceptance sidecar supersedes that draft status without modifying the reviewed artifact.',
 'first_batch_ledger_sha256_preserved':first_hash, 'date':'2026-10-29', 'accepted_at_utc':now,
 'external_actions_performed':False, 'path':'candidates/edge-irregulator', 'acceptance':'candidates/edge-irregulator/acceptance.json'
}
decision = dict(entry)
decision.update(root_inspection='Root read all component mathematical source files across integration, the final Result and manuscript TeX, and all four rendered final pages. Root fresh replay audited all 167 actual types/origins/axioms/flags. Independent final reviewer additionally read all 167 readable printed types. No claim that root manually read every expanded type.',
 final_review_sha256=sha(F/'review.md'), final_provenance_sha256=sha(F/'provenance.json'), frozen_files_reverified=145,
 root_replay='Own fresh source-only extraction via final packet build.sh; 14 modules,167 declarations,PDF and ZIP byte-identical. No new replay was needed after final review because all frozen bytes remain identical.')
dump(A/'ACCEPTANCE.json', decision)
dump(C/'acceptance.json', decision)
dump(P/'ADOPTION.json', {'utc':now,'status':'Final replay and current inventories adopted; see acceptance sidecar','acceptance':entry['parent_decision'],'freeze_verified':145,'counts':[8,38],'review_sha256':sha(F/'review.md')})
review = P.parent/'sol-lasso-max-preliminary-review-r1'
dump(L/'ADOPTION.json', {'utc':now,'status':'HOLD','credit':0,'review_sha256':sha(review/'review.md'),'provenance_sha256':sha(review/'provenance.json'),'frozen_files_verified':49,
 'root_decision':'Independent mathematics PASS adopted; no formal or paper investment. Universal optimized-source attribution, actual journal body, 2023 thesis/distinct SSD comparison, substantive Lemma2 bridge and bounded current prior coverage remain unresolved. Focused source-scope review delegated.',
 'scope':'Relaxed SPD Gaussian criterion only; witness is not a balanced two-level design. Supremum upper bound is weak <=27/125, sufficient for strict separation.',
 'registry_correction':'Preliminary older API behind response is not current absence. Root complete18:13:38 inventories are newer coherent dated evidence; lasso-specific body review remains pending.', 'counts':[8,38]})
ledger = json.loads((B/'ledger.json').read_text())
assert ledger['accepted_count']==7 and ledger['total_accepted_count']==37
assert [e['number'] for e in ledger['accepted']]==list(range(31,38))
ledger['accepted'].append(entry)
ledger.update(accepted_count=8,total_accepted_count=38,next_global_outcome_number=39)
dump(B/'ledger.json',ledger)
n=(B/'NEXT.md').read_text()
n=n.replace('Accepted **7/30 additional, 37/60 total**; next outcome38.','Accepted **8/30 additional, 38/60 total**; next outcome39.')
n=n.replace('Combined exact minimum, manuscript and audited packet delegated. Credit0. See','Combined exact minimum and packet now ACCEPTED as outcome38: root and independent final replay14 modules/167 declarations, four-page paper and ZIP reproduce byte-identically. See root-edge-irregulator-acceptance-r1/ACCEPTANCE.json. Earlier component record:')
n=n.replace('Root rational KKT/Schur/cubic bounds pass; independent review pending, credit0.\nActive Sol high/default: edge-irregulator manuscript/packet r1,\nlasso preliminary review r1 and fresh finite/arithmetic discovery r80.', 'Root rational KKT/Schur/cubic bounds and independent ordinary review pass; source scope, published/closest bodies, classical eligibility and current prior clearance remain HOLD, credit0. No Lean investment. See root-lasso-review-adoption-r1/ADOPTION.json.\nActive Sol high/default: lasso source-scope review r2, fresh finite/arithmetic discovery r80 and fresh analysis/probability discovery r81.')
(B/'NEXT.md').write_text(n)
r=(B/'RESULTS.md').read_text().replace('**7/30**','**8/30**').replace('**37/60**','**38/60**')
r=r.replace('\nEach acceptance has', '\n|38|Connected graphs with 8t edges and exact edge-irregulator minimum 3t; refutes the universal m/3+c bound|14 mathematical modules,167 declarations; root and independent extracted replay|[paper](candidates/edge-irregulator/paper.pdf), [decision](lanes/root-edge-irregulator-acceptance-r1/ACCEPTANCE.json)|\n\nEach acceptance has')
(B/'RESULTS.md').write_text(r)
dump(A/'active-delegates.json',{'utc':now,'model':'gpt-6.1-sol','reasoningEffort':'high','serviceTier':'default','tasks':['lasso-source-scope-sol-r2-20261029','fresh-source-discovery-sol-r80-20261029','fresh-source-discovery-sol-r81-20261029'],'no_polling':True})

# Explicit source/evidence pathspec; omit duplicate extraction trees and compiled caches.
selected={B/'ledger.json',B/'NEXT.md',B/'RESULTS.md',B/entry['packet']}
skip={'input','extracted','verification-final','verification-fresh','candidate-copy','consulted','paper-build','paper-cache','paper-tmp','__pycache__'}
for base in (A,C,L,S,F,review):
    for p in base.rglob('*'):
        rel=p.relative_to(base)
        if p.is_file() and not any(x in skip for x in rel.parts) and p.suffix not in {'.olean','.ilean','.o','.so','.ir','.pyc'}:
            selected.add(p)
for p in P.iterdir():
    if p.is_file() and p.name not in {'omega-tree.txt','openai-tree.txt'}: selected.add(p)
for p in (P/'current-bodies').rglob('*'):
    if p.is_file(): selected.add(p)
pathspec=A/'pathspec.txt'
selected.add(pathspec)
pathspec.write_text(''.join(str(p.relative_to(ROOT))+'\n' for p in sorted(selected)))
dump(A/'INTEGRITY.json',{'utc':now,'accepted_count':8,'total':38,'frozen_files':145,'lasso_frozen_files':49,'packet_sha256':sha(B/entry['packet']),'paper_sha256':sha(C/'paper.pdf'),'first_ledger_sha256':sha(first),'selected_paths':len(selected)})
with pathspec.open('a') as f:f.write(str((A/'INTEGRITY.json').relative_to(ROOT))+'\n')
assert sha(first)==first_hash
print(json.dumps({'accepted':38,'counts':[8,38],'selected_paths':len(selected)+1,'packet_sha256':sha(archive)}))
