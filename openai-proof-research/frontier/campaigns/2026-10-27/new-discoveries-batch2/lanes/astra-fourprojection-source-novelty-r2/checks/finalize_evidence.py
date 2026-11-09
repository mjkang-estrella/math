"""Create lane-local evidence summaries without modifying reviewed sources."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN = ROOT.parents[1]
REPO = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
PRIOR = ROOT.parent / 'astra-fourprojection-preliminary-review-r1'
CLONE = REPO / 'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'

def write(name, obj):
    (ROOT / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def digest(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}

def update_record(record, family, evidence, scope, assessment):
    record['previous_coverage'] = record['coverage']
    record['previous_assessment'] = record['assessment']
    record.update(review_round='source-novelty-r2', work_family=family, evidence=evidence,
                  coverage=scope, assessment=assessment, full_paper_read=False)

records = json.loads((PRIOR / 'sources/citation-coverage.json').read_text())
updates = {
 'Quantum Permutations and Quantum Reflections': ('vixra:2009.0045v1', ['sources/web-search-13.json', 'sources/web-search-8.json', 'sources/web-versions.json'], 'Actual PDF body through public web reader: targeted Theorems 12.7, 12.8, 12.10, 12.21 and surrounding argument; not full book', 'Stationarity/convolution and tensor-chain Gram moments; no target trace-normalization theorem found. Direct PDF download 406; no screenshot inspection claimed.'),
 'Modelling questions for transitive quantum groups': ('arxiv:1711.03206', ['sources/transitive-v5.pdf', 'sources/transitive-v4.pdf', 'sources/transitive-version.html'], 'v5 14 May 2020 pp.24–25,36; earlier v4 pp.23–25,36; targeted body and keyword screen', 'Proposition 8.5 is diagonal-unitary scaling; Theorem 8.7 is inner faithfulness. Latest v6 withdrawn as obsolete. No target found in inspected passages.'),
 'Stationarity questions for transitive quantum groups': ('arxiv:1711.03206', ['sources/transitive-v5.pdf', 'sources/transitive-version.html', 'sources/web-discovery.json'], 'Same-work title/version linkage; v5 targeted passages, not separate full historical-version reading', 'Same family as Modelling questions for transitive quantum groups; not independently counted work. Historical versions not all compared.'),
 'Quasi-flat representations of uniform groups and quantum groups': ('arxiv:1708.09683', ['sources/quasiflat.pdf'], 'v3 31 March 2018 pp.1–3,5–7, relevant definitions and theorem statements', 'Uniform-root spectra, universal quasi-flat representations and integration/faithfulness; no paired MP trace descent result found.'),
 'Faithful matrix models for discrete quantum groups': ('arxiv:1708.09683', ['sources/quasiflat.pdf', 'sources/web-discovery2.json'], 'Same-work title linkage to arxiv 1708.09683; targeted v3 body, not separate full historical-version reading', 'Not an independent body; no paired MP trace descent in inspected v3 passages. Historical versions not all compared.'),
 'Isolated Partial Hadamard Matrices and Related Topics': ('arxiv:1706.00986v2', ['sources/isolated-hadamard.pdf'], 'v2 pp.20–24 plus whole-text term/theorem inventory screen', 'Proposition 5.6, Theorem 5.9, Theorem 6.1 and closing isolation conjectures have different endpoints.'),
 'Complex Hadamard matrices with noncommutative entries': ('arxiv:1705.10264v2', ['sources/noncommutative-hadamard.pdf'], 'v2 pp.7–8,10–11; Theorem 3.2 full statement and three-step proof read', 'Magic matrix construction uses Hadamard unitarity/commutation; not arbitrary four-projection positive-root normalization.'),
 'Thoma type results for discrete quantum groups': ('arxiv:1705.07050v2', ['sources/thoma.pdf'], 'v2 pp.6–7 Proposition 2.6 and proof, pp.15–16 quasi-flat conclusion, plus theorem inventory', 'Integration-preserving representation via finite-coindex quotient, and stationarity/type-I questions; no target bridge found.'),
 'Quantum groups from stationary matrix models': ('arxiv:1604.03756v3', ['sources/stationary.pdf'], 'v3 pp.16–20 Theorem 5.5, Theorem 6.2, Conjecture 6.3; theorem/term inventory elsewhere', 'Stationary Haar models and inner faithfulness, not the target normalization potential.'),
 'Deformed Fourier models with formal parameters': ('arxiv:1603.09433v2', ['sources/deformed-fourier.pdf'], 'v2 pp.1–2,21 including Theorem 9.1 and final discussion; term screen elsewhere', 'Character-law support and free-Poisson asymptotics, no paired normalization inequality in inspected material.'),
 'Introduction to compact (matrix) quantum groups and Banica–Speicher (easy) quantum groups': ('doi:10.1007/s12044-017-0362-3', ['sources/weber-springer-pdf.response', 'sources/weber-springer-pdf.txt'], 'Actual published PDF; printed pp.924,926–929, source citation and final questions; related categorical passages; whole-text term screen', 'The source is reference [27], cited with other matrix-model work. No target resolution found. Both DOI records share one body. arxiv1603.09192 is a wrong-paper lead and excluded.'),
}
new_count = 0
for record in records:
    if record['title'] in updates:
        update_record(record, *updates[record['title']])
        new_count += 1
    elif 'Easy quantum groups :' in record['title']:
        record.update(review_round='source-novelty-r2', coverage='Attempted, actual thesis body remains unread',
                      assessment='SULB landing and thesis file 403; web retrieval failed. Abstract and related article do not replace thesis.',
                      evidence=['sources/jung-landing.html','sources/jung-thesis.pdf'], full_paper_read=False)
    else:
        record['review_round'] = 'inherited preliminary review; not reread here'
        record['evidence_report'] = str(PRIOR / 'review.md')
write('sources/citation-coverage.json', records)
write('sources/coverage-summary.json', {
    'corpus_records':len(records), 'inherited_body_covered_records':13,
    'new_body_covered_records':new_count, 'total_at_least_partial_body_coverage':13+new_count,
    'still_unread_records':1, 'new_distinct_work_families':len({updates[r['title']][0] for r in records if r['title'] in updates}),
    'limits':'Record count includes duplicates and same-work title/version linkage; not full-paper or exhaustive historical-version reading.',
    'additional_closest_matrix_paper':{'id':'arxiv:2507.14940v2','authors':['Zongben Xu','Teng Zhang'], 'date':'2026-09-29',
        'evidence':['sources/sharp-polar-v2.pdf','sources/sharp-polar-page3.png'],
        'scope':'Main statements pp.1–6, basic convexity/substochastic lemmas pp.7–8; p.3 visually checked.',
        'result':'No complete subsumption bridge; direct sharp polar-factor bound has unbounded constant on admissible frame spectra.'}
})

inputs = [REPO/'AGENTS.md', CAMPAIGN/'AGENTS.md', CAMPAIGN/'ledger.json', CAMPAIGN/'prior-campaign-context.json',
          PRIOR/'review.md', PRIOR/'sources/citation-coverage.json',
          ROOT.parent/'root-fourprojection-r1/preliminary-review-hashes.json']
write('sources/provenance.json', {
    'created_utc':datetime.now(timezone.utc).isoformat(),
    'candidate_label_supplied_by_user':'74f23e9fb2', 'candidate_lane':'root-fourprojection-r1',
    'candidate_hash_entry_count_inherited':46,
    'candidate_integrity_scope':'Previous independent review reported 46/46 matches. This pass identifies and hashes the supplied manifest; does not rerun candidate verification or git.',
    'input_files_current_hashes':[digest(p) for p in inputs],
    'writes_confined_to':str(ROOT), 'children':0, 'git_commands':0, 'lean_invocations':0,
    'source_verdict':'HOLD', 'novelty_verdict':'HOLD', 'acceptance_or_count_change':False,
    'credentials_or_challenge_bypass':False,
    'old_clone':{'path':str(CLONE),'head':(CLONE/'.git/HEAD').read_text().strip(), 'ref_value':(CLONE/'.git/refs/heads/dev').read_text().strip()}
})

raw = (ROOT/'sources/trureturing-matches.txt').read_text()
patterns={'banica':'banica','exact_mathdb_id':r'\b332493\b','arxiv_id':r'1602\.04456',
          'nechita':'nechita','sinkhorn':'sinkhorn','polar':'polar','four_projection':r'four.?projection'}
nearby=['Library/QuantumContext/devos2014scalingunitary.md','Blueprint/D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.md']
write('sources/trureturing-screen.json', {
 'clone_revision':(CLONE/'.git/refs/heads/dev').read_text().strip(),
 'raw_results':'sources/trureturing-matches.txt',
 'search_pattern':r'banica|nechita|332493|1602[.]04456|four.?projection|sinkhorn|polar.{0,30}(orthogon|contract)|orthogon.{0,30}polar',
 'file_globs':['*.md','*.lean','*.tex','*.json','*.txt'],
 'counts_in_saved_matching_lines':{name:len(re.findall(pat,raw,re.I)) for name,pat in patterns.items()},
 'nearby_full_texts_read':[digest(CLONE/p) for p in nearby],
 'limits':'Checked-out content only, no history search, no full theorem audit, no replay. Numeric substring hits in long JSON are not exact problem-ID matches.'})

retrievals=json.loads((ROOT/'sources/retrievals.json').read_text())
selected=['publisher-official-pdf.response','publisher-official-xml.response','publisher-fullview.response','archive-availability.json','openAIRE.json']
classification={'publisher-official-pdf.response':'403; no body', 'publisher-official-xml.response':'200 metadata/coredata only',
                'publisher-fullview.response':'401 AUTHENTICATION_ERROR Invalid API Key; stopped',
                'archive-availability.json':'429; stopped with no retry', 'openAIRE.json':'200 metadata; no new attached journal body'}
write('sources/source-route-assessment.json', {'verdict':'HOLD','actual_published_conjecture_read':False,
      'routes':[dict(r,assessment=classification[r['name']]) for r in retrievals if r['name'] in selected],
      'inherited_routes_report':str(PRIOR/'review.md'),
      'limits':'Searches exhausted stated leads, not every public repository. No metadata/arxiv equivalence clearance.'})

assert len(records)==26 and new_count==12
for r in retrievals:
    if 'path' in r:
        assert hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest()==r['sha256'], r['name']
write('checks/evidence-validation.json', {'status':'PASS','retrieval_hashes_verified':sum('path' in r for r in retrievals),
      'coverage_records':26,'new_partial_body_coverage':12,'total_partial_body_coverage':25,
      'scope':'Evidence packaging consistency only. No mathematical, source-body equivalence, novelty or formal acceptance certification.'})
print(json.dumps({'records':26,'new':new_count,'verdicts':['SOURCE HOLD','NOVELTY HOLD']}))
