"""Bind the completed final extracted replay before changing accounting."""
from pathlib import Path
import hashlib, json, shutil, zipfile
from datetime import datetime, timezone

A = Path(__file__).resolve().parent
B = A.parents[1]
C = B / 'candidates/jacobi-shifted-denominator'
P = B / 'lanes/root-jacobi-final-preparation-r1'
V = B / 'lanes/sol-jacobi-full-final-review-r1'
packet = B / 'candidate-packets/2026-remark38-jacobi-shifted-denominator-proof.zip'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = json.loads((A/'final-extracted/extraction-receipt.json').read_text())
assert receipt['status'] == 'PASS'
assert receipt['mathematical_module_count'] == 35
assert receipt['all_isUnsafe_false'] is True
assert receipt['pins_before_after_equal'] is True
assert receipt['full_generated_origin_declaration_count'] == 1041
assert receipt['packet_sha256'] == sha(packet)
assert receipt['payload_hashes_before_after_verified'] is True
assert receipt['immutable_payload'] is True
with zipfile.ZipFile(packet) as z:
    manifest = json.loads(z.read('manifest.json'))
    assert len(manifest) == 238
    assert set(z.namelist()) == set(manifest) | {'manifest.json'}
    for n,h in manifest.items():
        assert hashlib.sha256(z.read(n)).hexdigest() == h, n
        assert sha(C/n) == h, n
assert packet.read_bytes() == (A/'regenerated.zip').read_bytes()
reviewed = json.loads((A/'reviewed-payload-manifest.json').read_text())
for n,h in reviewed.items():
    if n.startswith(('formal/','scripts/')) or n in ['component.json','pins.json','FORMAL-MAP.md']:
        assert manifest[n] == h, n
for n,h in json.loads((P/'review-freeze.json').read_text())['files'].items():
    assert sha(P/n) == h, n
logdir = A/'final-extracted/build/formal'
other = V/'fresh-replay/build/formal'
logs = sorted(logdir.glob('*.lean.log'))
assert len(logs) == 39, len(logs)
for log in logs:
    assert log.read_bytes() == (other/log.name).read_bytes(), log.name
declarations = json.loads((A/'final-extracted/build/declarations.json').read_text())
shutil.copyfile(A/'final-extracted/extraction-receipt.json', A/'final-extracted-receipt.json')
shutil.copyfile(A/'final-extracted/build/declarations.json', A/'final-declarations.json')
shutil.copyfile(logdir/'WholeAudit.lean.log', A/'final-WholeAudit.log')
shutil.copyfile(logdir/'ExpandedEndpoint.lean.log', A/'final-ExpandedEndpoint.log')
first = B.parents[1]/'2026-10-26/new-discoveries/ledger.json'
baseline = '4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385'
assert sha(first) == baseline
now = datetime.now(timezone.utc).isoformat()
entry = {
    'number':33,
    'status':'ACCEPT: full shifted all-order source question; independent final review and final extracted replay PASS, with bounded novelty limits',
    'discovery_count_credit':1,
    'title':'Exact dyadic denominator law in shifted Jacobi parameters',
    'source_target':'Area, arXiv:2608.23006v2, Definition 2.1, equations (6)-(7), Remark 3.8',
    'source_url':'https://arxiv.org/html/2608.23006v2',
    'scope':'For every integer r>=1, the maximal dyadic denominator exponent of the literal kappa_r(u,v) is 2r+v2((r-1)!). Every coefficient satisfies the upper bound and the nonzero pure-u^r coefficient attains it. Odd denominator factors are allowed.',
    'mathdb_scope_note':'391922 concerns the already-public original-variable law, not this shifted question. No new record or solution link is asserted.',
    'formal_modules':35,
    'formal_declarations':1041,
    'declaration_inventory_scope':'Every actual mathematical-module-origin declaration, including private/generated declarations and instances; four audit/display modules are outside mathematical origins.',
    'allowed_axioms':['Classical.choice','Quot.sound','propext'],
    'endpoint':'JacobiShifted.source_claim : JacobiShifted.SourceClaim',
    'packet':str(packet.relative_to(B)), 'packet_sha256':sha(packet),
    'paper':str((C/'paper.pdf').relative_to(B)), 'paper_sha256':sha(C/'paper.pdf'),
    'manifest_sha256':sha(C/'manifest.json'),
    'receipt_sha256':sha(A/'final-extracted-receipt.json'),
    'final_extracted_receipt':str((A/'final-extracted-receipt.json').relative_to(B)),
    'parent_decision':str((A/'ACCEPTANCE.md').relative_to(B)),
    'independent_reviews':['lanes/sol-jacobi-full-preliminary-review-r1/review.md','lanes/sol-jacobi-full-final-review-r1/review.md'],
    'postreview_manuscript_change':'Publication/status wording only; all formal sources, verifier scripts and mathematical content unchanged. All six final pages inspected. Added final review evidence.',
    'novelty_limit':'Current primary/companion bodies and complete public-registry trees checked; no matching prior resolution or complete classical subsumption bridge identified. Classical filtered Riccati/Gelfand-Dikii/primitive literature not exhaustively body-read; no universal priority claim.',
    'one_family':'Full shifted law only. Original-variable law, Area binomial valuation, top-coefficient attainment, degree/parity, classical helpers and formalization are not separate credits. All-order analytic phase identification is not asserted.',
    'first_batch_ledger_sha256_preserved':baseline,
    'date':now[:10], 'accepted_at_utc':now,
    'external_actions_performed':False,
    'path':str(C.relative_to(B)),
    'acceptance':str((C/'acceptance.json').relative_to(B))
}
decision = '''# Root acceptance decision: outcome 33 — shifted Jacobi denominator law

ACCEPT ONE outcome: for every integer r >= 1, the exact dyadic part of the
common denominator of Area's literal formal kappa_r in independent shifted
parameters u,v is 2^(2r + nu_2((r-1)!)). The upper bound covers every monomial;
the actual nonzero pure-u^r coefficient attains it. Odd denominator factors
are allowed. This resolves Remark 3.8 of arXiv:2608.23006v2, not the already
public original-variable law or an all-order analytic phase identification.

Source: actual current primary Definition 2.1, (6)-(7), Remark 3.8 and companion
2609.29531v2 were inspected by root and independent reviewers. Both are public
preprints; no journal publication is invented. The half substitution and literal
finite logarithm are part of the certificate. MathDB 391922 is not a new target.

Mathematics: the literal source equation is proved before its finite log/Riccati
identification. The binary filtration requires two separate quadratic pairings,
not a false arbitrary-product closure. Integral parity and ideal extraction,
odd triangular primitive inversion, and the derivative kernel remove a possible
integration constant. The actual half substitution costs 2^degree; the degree
bound and Legendre identity give the uniform result. The Catalan top layer and
literal pure coefficient yield sharpness using Area's already-known valuation.
All these bridges are proved internally, including the credited valuation.

Formal: root and independent reviewer each replayed the reviewed archive from
source; root then replayed the FINAL post-status-edit archive in another fresh
extraction. All 35 mathematical modules and four audit/display modules passed.
The actual-origin inventory covers 1,041 declarations including private and
generated helpers, with all safety flags false and only subsets of propext,
Classical.choice and Quot.sound. The closed endpoint has no residual premises.
The complete reports are mechanically checked block-by-block; semantic review
of actual mathematical sources and endpoint types is distinct from a claim to
manually audit every generated implementation type. Final 39 logs reproduce the
independent review logs byte-for-byte. Lean 4.34.1 binary/version and all nine
manifest packages, clean tracked states, and immutable payload hashes were
asserted before/after. Mathlib build caches are external pinned prerequisites.

Independent final review: root read the complete report and completed thread,
including its strongest classical-subsumption objection and candid limits.
The reviewer independently rebuilt ZIP/PDF, replayed all sources, inspected six
paper pages and refreshed both public proof registries to complete current trees.
No blocking issue was found. The optional 'published' wording is now explicitly
'public-preprint'. Frozen reviewed artifacts remain unchanged.

Substantive adjudication: a routine corollary can be excluded even if its general
theorem uses different objects; an explicit same-object theorem is not required
for exclusion. Here no established complete reduction has been identified.
Classical Riccati/Catalan and binary arithmetic alone do not provide the selected
midpoint primitive gain, normalized literal identification and full mixed-term
upper bound. Root accepts the assembled resolution of this distinct source
question as substantive, not its proof length or declaration count. The known
original-variable law and binomial valuation remain credited to Area. Top
attainment, parity/degree, helper lemmas and formalization receive no extra count.

Novelty remains bounded: current primary/companion versions, actual nearby
registry claims and relevant classical comparisons were screened. No complete
prior resolution or usable subsumer was found. Not every GD/WKB paper, registry
theorem, subscription index or citation body was read. This is not a universal
absence-of-prior-art or worldwide-priority certification. Relevant chronology
is retained in the independent report and current-prior evidence.

Final packet: 238 payload files plus relative manifest; two deterministic
serializations agree. No compiled proof artifacts are shipped. All mathematical
Lean sources, verifier scripts, pins and mathematical TeX remain unchanged from
the review. Only status/publication prose and final review evidence changed.
All six final pages were visually inspected; no clipping, overlap or overfull
boxes. Final archive/PDF/manifest/replay hashes are bound by acceptance.json.
Historical failed attempts and preliminary statuses remain explicitly historical.

Accounting: 3/30 additional, 33/60 total. First thirty and outcomes 31/32 remain
unchanged. No external upload, publication, contact or MathDB mutation occurred.
The additional-thirty goal remains active.
'''
(A/'ACCEPTANCE.md').write_text(decision)
(C/'acceptance.json').write_text(json.dumps(entry,indent=2,ensure_ascii=False)+'\n')
ledger_path=B/'ledger.json';ledger=json.loads(ledger_path.read_text())
assert ledger['accepted_count']==2 and ledger['total_accepted_count']==32
assert [x['number'] for x in ledger['accepted']]==[31,32]
old_accepted=json.dumps(ledger['accepted'],sort_keys=True)
ledger['accepted'].append(entry);ledger['accepted_count']=3;ledger['total_accepted_count']=33;ledger['next_global_outcome_number']=34
target=next(x for x in ledger['candidates'] if x['id']=='jacobi-shifted-denominator-remark38')
target.update(credit=1,status='ACCEPTED outcome33; full all-order literal theorem, independent final review and final extracted packet replay PASS',formal_status='PASS35 mathematical modules/1041 actual-origin declarations; standard3 only; closed source_claim',accepted_number=33,blocking_gates=[],independent_final_review='lanes/sol-jacobi-full-final-review-r1/review.md',final_candidate=entry['path'],acceptance=entry['acceptance'],packet=entry['packet'],packet_sha256=entry['packet_sha256'])
assert json.dumps(ledger['accepted'][:2],sort_keys=True)==old_accepted
assert sum(x['discovery_count_credit'] for x in ledger['accepted'])==3
ledger_path.write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'accepted':33,'additional':'3/30','total':'33/60','packet_sha256':sha(packet),'paper_sha256':sha(C/'paper.pdf'),'receipt_sha256':sha(A/'final-extracted-receipt.json'),'all_39_logs_match_independent_review':True},indent=2))
