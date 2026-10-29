import datetime, hashlib, json, pathlib, shutil

B = pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
A = B / 'lanes/root-polyomino57-acceptance-r1'
E = A / 'final-reproduction/extracted'
F = B / 'lanes/root-polyomino57-final-review-freeze-r1'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p, value):
    p.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger = json.loads((B/'ledger.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number']) == (6,36,37)
old = json.loads(json.dumps(ledger['accepted']))
baseline = pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/ledger.json')
baseline_hash = '4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385'
assert sha(baseline) == baseline_hash
manifest = json.loads((E/'source-manifest.json').read_text())
assert len(manifest) == 2023
for name, record in manifest.items():
    assert sha(E/name) == record['sha256']
    assert (E/name).read_bytes() == (F/'extracted'/name).read_bytes(), name
assert (E/'source-manifest.json').read_bytes() == (F/'extracted/source-manifest.json').read_bytes()
assert sha(A/'final-edition.zip') == 'a931d2d92f70c9bfc774fe6c441787cc95e8e5a6d57c7c13a4805857527f5796'
assert sha(E/'paper.pdf') == 'c3ea0ccb3e68b1564a9acbf3a639d0c632d3016d56bf2981cb33e8f81be81d54'
assert sha(F/'ROOT-REPLAY-RECEIPT.json') == 'f42c3e8d16d0acae5fde6e7770d0cbc8b236ee787b089931289e920c1659ec79'
repro = json.loads((A/'final-reproduction/REPRODUCTION.json').read_text())
assert repro['status']=='PASS' and repro['PDF_byte_identical'] and repro['ZIP_byte_identical']
save(A/'FINAL-SOURCE-BINDING.json', dict(utc=now,status='PASS',formal_files=2023,all_final_extracted_sources_byte_identical_to_root_fresh_replay=True,source_manifest_sha256=sha(E/'source-manifest.json'),root_replay_receipt_sha256=sha(F/'ROOT-REPLAY-RECEIPT.json'),root_final_reproduction_receipt_sha256=sha(A/'final-reproduction/REPRODUCTION.json'),qualification='Full fresh Lean replay ran on the earlier extracted archive; every Lean source is byte-identical in this final status-only edition. Final archive extraction, manifest verification and PDF/ZIP reproduction rerun; no redundant new Lean replay claimed.'))
novelty = {
    'utc': now, 'status': 'Bounded acceptance screen; no known matching resolution, not exhaustive current-head clearance',
    'source': 'https://oeis.org/A395495',
    'source_read': 'Actual current entry specifies translation-only fixed polyominoes, connected container, holes allowed, and formula for every n>=4; read before acceptance.',
    'web_evidence_sha256': sha(A/'acceptance-web-evidence.txt'),
    'latest_observed_omega_head': '6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3',
    'closest_primary_reread': 'Problems/condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence.md and D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean at that immutable head',
    'scope_comparison': 'Minimum board containing N translations of one specified L n-omino differs from a board containing every fixed 11-omino. Actual claim and definitions read; no subsumption bridge.',
    'tree_correction': 'r57 omega-D5.json is Blueprint/D5 markdown, not the actual Lean D5 tree. Its lexical stem comparison with the final-review Lean tree is not a content/hash delta verification.',
    'stem_comparison_only': ['S1/Dynamics/MinimalFlowDilationMixing','S3/Weil/Mertens/CriticalThetaTailPeak'],
    'limits': ['No complete post-3b4135 actual Lean-tree delta clearance; current API head refresh blocked with HTTP403 and not bypassed.', 'Author code unavailable; fresh history gap remains, cached history read.', 'Targeted current web searches found no matching construction; search absence is not a proof of priority.', 'Complete named saved trees and independent final-review checks are bounded evidence, not worldwide absence.'],
    'root_judgment': 'Accept with these material limits recorded; no positive prior proof or routine complete bridge located. Reopen if a relevant earlier construction is produced.'}
save(A/'ACCEPTANCE-PRIOR-LIMITS.json',novelty)
dst=B/'candidates/polyomino57'
assert not dst.exists()
shutil.copytree(E,dst)
packet=B/'candidate-packets/A395495-polyomino57-counterexample.zip'
assert not packet.exists()
shutil.copy2(A/'final-edition.zip',packet)
record={
 'number':37,'status':'ACCEPT: full literal formula refutation; independent review, root fresh Lean replay and final-edition identity/reproduction PASS; substantive dissent and bounded novelty limits retained',
 'discovery_count_credit':1,'title':'A 57-cell connected container for every fixed 11-omino',
 'source_target':'Peter Exley, OEIS A395495, universal formula for n>=4', 'source_url':'https://oeis.org/A395495',
 'scope':'The connected integer-cell witness C={|x|+|y|<=5} minus {(2,2),(2,-2),(-2,2),(-2,-2)} has 57 cells and contains every fixed 11-omino by translation. Thus a(11)<=57<58, refuting the universal formula.',
 'scope_limit':'No optimality of 57, first failing n, asymptotic family, general algorithm, or separate helper credit.',
 'formal_modules':2022,'audit_modules':1,'formal_declarations':5924,
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'all_actual_unsafe_flags_false':True,
 'compiler_partial_exception':{'name':'Polyomino57.attachCheck._unsafe_rec','unsafe':False,'partial':True,'axiom':False,'note':'Inherited compiler artifact; safe total logical checker and soundness proved. No all-partial-false claim.'},
 'endpoint':'Polyomino57.Diagonal.FiniteProof.AllCases.universalContainer : UniversalContainer 11 witness',
 'source_refutation':'Polyomino57.Diagonal.FiniteProof.AllCases.source_refutation : ¬ SourceFormula',
 'packet':str(packet.relative_to(B)),'packet_sha256':sha(packet),'paper':'candidates/polyomino57/paper.pdf','paper_sha256':sha(dst/'paper.pdf'),
 'manifest_sha256':sha(dst/'MANIFEST.json'),'source_manifest_sha256':sha(dst/'source-manifest.json'),
 'receipt_sha256':sha(F/'ROOT-REPLAY-RECEIPT.json'),
 'final_extracted_receipt':'lanes/root-polyomino57-acceptance-r1/final-reproduction/REPRODUCTION.json',
 'final_source_binding':'lanes/root-polyomino57-acceptance-r1/FINAL-SOURCE-BINDING.json',
 'parent_decision':'lanes/root-polyomino57-acceptance-r1/ACCEPTANCE.json',
 'independent_reviews':['lanes/sol-polyomino57-preliminary-review-r1/review.md','lanes/sol-polyomino57-compressed-review-r1/review.md','lanes/sol-polyomino57-full-final-review-r1/review.md'],
 'standing_dissent':'lanes/sol-polyomino57-source-prior-refresh-r3/review.md',
 'postreview_manuscript_change':'Status prose and final review/replay evidence only. All 2023 Lean sources and 5924 actual declaration records unchanged. Root visually inspected all seven final pages; final PDF and ZIP reproduce byte-identically.',
 'novelty_limit':novelty['limits'],
 'substantive_adjudication':'One full intended universal-formula refutation at interior n=11. No inspected classical tree-center or punctured-diamond construction proves57 (classical tree-center gives61). Standing dissent: narrow finite optimization against recent extrapolation, with no optimum or scalable family. Root accepts the literal full refutation; search, computation size, proof engineering and quota earn no significance credit.',
 'one_family':'One universal-container formula refutation; all 70 finite cases, tables and certificates are uncredited auxiliaries.',
 'resource_limit':'Heavy checks capped; root replay peak sampled2775.223MiB<2800MiB, 45ms sampling cannot exclude unsampled transients. Historical small text/metadata helpers lacked explicit caps; Node PDF marker failed under AS512MiB, no cap increase. These deviations are retained, not all-protocol PASS.',
 'first_batch_ledger_sha256_preserved':baseline_hash,'date':'2026-10-29','accepted_at_utc':now,
 'external_actions_performed':False,'path':'candidates/polyomino57','acceptance':'candidates/polyomino57/acceptance.json'}
save(A/'ACCEPTANCE.json',record)
save(dst/'acceptance.json',record)
ledger['accepted'].append(record)
ledger.update(accepted_count=7,total_accepted_count=37,next_global_outcome_number=38)
assert ledger['accepted'][:-1]==old and sha(baseline)==baseline_hash
save(B/'ledger.json',ledger)
results=(B/'RESULTS.md').read_text().replace('**6/30**','**7/30**').replace('**36/60**','**37/60**')
needle='\nEach acceptance has independent adversarial review'
row='\n|37|Connected 57-cell universal container for every fixed 11-omino; refutes OEIS A395495 formula|2,022 mathematical modules,5,924 declarations; root fresh replay bound to identical final sources|[paper](candidates/polyomino57/paper.pdf), [decision](lanes/root-polyomino57-acceptance-r1/ACCEPTANCE.json)|\n'
assert needle in results
results=results.replace(needle,row+needle)
(B/'RESULTS.md').write_text(results)
nextfile=B/'NEXT.md'
history=nextfile.read_text().split('## Historical continuation notes',1)[1]
nextfile.write_text('''# Current continuation — 29 October 2026

Accepted **7/30 additional, 37/60 total**. Outcome37 is the connected 57-cell
container for every fixed 11-omino, proving a(11)<=57<58 and refuting OEIS A395495.
No optimality or general asymptotic claim. Root acceptance:
lanes/root-polyomino57-acceptance-r1/ACCEPTANCE.json.
Independent final review, root fresh 2022-module/5924-record replay, final-source
byte identity and final PDF/ZIP reproduction pass. Substantive dissent, current
registry freshness gaps and resource-protocol qualifications remain explicit.
No external publication, upload or MathDB change.

Bessel-ratio literal series and generic one-crossing formal components are in
separate Sol high/default lanes. Ordinary proof and provisional investment pass;
novelty remains HOLD and credit0. Fresh r59 Ferrers-rook research completed
unresolved, credit0, awaiting root handback processing. Continue new full-scope
research with up to three useful workers, no children, honoring all exclusions.
Do not treat older pinned registry searches as complete current-head coverage.

## Historical continuation notes'''+history)
paths=[B/'ledger.json',B/'RESULTS.md',B/'NEXT.md',packet,dst,A/'ACCEPTANCE.json',A/'ACCEPTANCE-PRIOR-LIMITS.json',A/'FINAL-SOURCE-BINDING.json',A/'acceptance-web-evidence.txt',A/'accept.py',A/'final-reproduction/REPRODUCTION.json']
(A/'acceptance-pathspec.txt').write_text('\n'.join(str(p) for p in paths)+'\n')
save(A/'TRANSACTION-CHECK.json',{'status':'PASS','accepted_count':7,'total_accepted_count':37,'next_global_outcome_number':38,'previous_six_records_unchanged':True,'first_batch_ledger_unchanged':True,'final_source_files_verified':2023,'final_pdf_pages_root_visually_read':7,'utc':now})
with (A/'acceptance-pathspec.txt').open('a') as f: f.write(str(A/'TRANSACTION-CHECK.json')+'\n')
print('PASS: outcome37 acceptance; prior six and first batch unchanged; final source identity2023; counts7/37')
