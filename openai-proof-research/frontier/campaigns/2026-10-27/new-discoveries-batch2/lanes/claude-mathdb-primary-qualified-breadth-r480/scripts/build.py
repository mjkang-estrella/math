# Assemble r480 deliverables from original corpus chunks (read in place), retained sources and table.py.
import json, hashlib, os, re, sys
O = sys.argv[1]; L = os.path.dirname(O)
sys.path.insert(0, os.path.join(O, 'scripts'))
from table import T, REG
CORP = os.path.join(L, 'pi-mathdb-full-corpus-inventory-r301')
INT = os.path.join(L, 'root-mathdb-breadth-intake-r479')
def sha(p):
    b = open(p, 'rb').read(); return hashlib.sha256(b).hexdigest(), len(b)
def canon(r): return hashlib.sha256(json.dumps(r, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode('utf-8')).hexdigest()
res = json.load(open(os.path.join(INT, 'reserved-ids.json')))
ids = res['ids']; S = set(ids)
assert len(ids) == 50 and set(T) == S, (len(ids), S ^ set(T))
# locate records in original chunks
found = {}
for k in range(1, 21):
    fn = 'corpus/mathdb-normalized-chunk-%04d.jsonl' % k
    with open(os.path.join(CORP, fn), 'rb') as f:
        for ln, raw in enumerate(f, 1):
            if b'"mathdb_id"' not in raw: continue
            r = json.loads(raw)
            if r['mathdb_id'] in S:
                assert r['mathdb_id'] not in found
                found[r['mathdb_id']] = (fn, ln, r)
assert set(found) == S
# fetch log -> retained sources
log = [l.split() for l in open(os.path.join(O, 'sources', 'fetch-log.txt')) if ' OK ' in l]
ret = {}
for p in log:
    t, a, _, code, url, ctype, h, n = p[:8]
    pdf = os.path.join(O, 'sources', 'arxiv', a + '.pdf'); txt = pdf[:-4] + '.txt'
    hh, nn = sha(pdf); assert (hh, nn) == (h, int(n)), a
    th, tn = sha(txt)
    text = open(txt, encoding='utf-8', errors='replace').read()
    m = re.search(r'arXiv:' + re.escape(a) + r'v\d+', text)
    ret[a] = dict(arxiv=a, url='https://arxiv.org/pdf/' + a, retrieved_utc=t, http_status=int(code), final_url=url, content_type=ctype,
                  pdf_path='sources/arxiv/%s.pdf' % a, pdf_sha256=h, pdf_bytes=int(n), bound_before_reading=True,
                  text_path='sources/arxiv/%s.txt' % a, text_sha256=th, text_bytes=tn, text_tool='pdftotext -layout (guarded)',
                  version_stamp=m.group(0) if m else None, used_by=[])
disp = []
LEVEL = {
 'qualified_brief_screening_only': 'complete candidate argument written; bounded decisive check run; not independently reviewed',
 'retained_argument_routine_bridge_not_qualified': 'complete short argument written; classified routine (explicit classical bridge)',
 'exclude_source_internal_proof': 'source states a proof of the literal statement; proof body NOT audited',
 'exclude_literal_transcription_defect': 'literal refuted by source-internal lemma (typo-level); no mathematics credited',
 'park_equivalent_major_open': 'source-internal equivalence theorem statement and proof passage read',
 'hold_suspected_public_resolution': 'no proof attempted; suspected later public resolution from memory only (UNVERIFIED)',
 'park_deep_open': 'no proof attempted (deep/famous open)',
 'park_no_tractable_mechanism': 'no proof attempted beyond screening; no tractable mechanism found',
}
for i in ids:
    fn, ln, r = found[i]
    a, rx, d, reason = T[i]
    text = open(os.path.join(O, 'sources', 'arxiv', a + '.txt'), encoding='utf-8', errors='replace').read().split('\n')
    sl = next((k + 1 for k, l in enumerate(text) if re.search(rx, l)), None)
    assert sl is not None, (i, rx)
    assert ('arxiv.org/abs/' + a) in r['source_url'], i
    ret[a]['used_by'].append(i)
    disp.append(dict(
        mathdb_id=i, title=r['title'], literal_statement=r['statement'],
        statement_utf8_sha256=hashlib.sha256(r['statement'].encode('utf-8')).hexdigest(),
        original_chunk=fn, original_line=ln, canonical_record_sha256=canon(r),
        record_source_url=r['source_url'], record_status=r['status'], record_solution_count=r['solution_count'],
        disposition=d, reason=reason,
        source_evidence_level='selected primary passage read: %s line %d of retained text (pattern %r); whole body NOT read' % (ret[a]['version_stamp'], sl, rx),
        source_passage=dict(arxiv=a, version=ret[a]['version_stamp'], text_line=sl),
        literal_review='literal record statement read in full and compared with primary passage',
        proof_evidence_level=LEVEL[d],
        concluding_proof_section_read=False, dependency_audit=False,
        prior_evidence_level=REG, full_prior_subsumption_coverage=False,
        accepted_credit=0))
json.dump(disp, open(os.path.join(O, 'dispositions.json'), 'w'), ensure_ascii=False, indent=1)
json.dump(sorted(ret.values(), key=lambda x: x['arxiv']), open(os.path.join(O, 'retained-sources.json'), 'w'), ensure_ascii=False, indent=1)
# proposals
B = lambda f: dict(path='briefs/' + f, sha256=sha(os.path.join(O, 'briefs', f))[0])
props = dict(
 accepted_credit=0, new_mathematics_credited=0,
 note='Screening stage. Briefs are candidate arguments retained for separate independent hypothesis review; no credit, no novelty clearance.',
 qualified_briefs=[
  dict(id='P1', mathdb_id=338290, kind='counterexample', source='arXiv:1801.08029v2 Conjecture 3.8',
       quantifiers='all positive weights w_1..w_m, all quotas q (any voting game), all players i: beta_i <= 2w/N',
       mechanism='dominant player with one-short quota: weights (k;1^{k+1}), q=k+1, gamma_big=2^{k+1}-2, gamma_small=2',
       decisive_calculation='exact: absolute (3;1^4),q=4: 7/8>6/7; normalized (7;1^8),q=8: 127/135>14/15; exhaustive m<=9,w<=8 search',
       certificate_size='one 9-player game, 512 coalitions', formal_dependencies='Finset counting; decide on Fin 9 subsets',
       runs=['runs/banzhaf.r1.txt'], brief=B('P1-338290-banzhaf-counterexample.md'), prior='HOLD', accepted_credit=0),
  dict(id='P2', mathdb_id=339564, kind='proof', source='arXiv:1806.06821v2 Conjecture 4.4',
       quantifiers='all n with (n,6)=2, n>=8',
       mechanism='d(A)=max_p deg gcd_Fp(t^n-1,1+t+t^{m-1}); roots satisfy zeta^m=+-1 => x^2+x-+1; p=3 order-8 roots; Lucas L_m+2 prime factors',
       decisive_calculation='integer SNF of n x n circulant for all admissible n<=160 (52 values) matches; Theorem 4.2 misprint detected',
       certificate_size='short case analysis (~1 page) + standard Lucas residue periods', formal_dependencies='abelianisation of cyclic presentation as Z[t]/(t^n-1,f); finite abelian d(A); polynomial gcd over F_p',
       runs=['runs/abel_snf.8-64.r1.txt', 'runs/abel_snf.65-160.r1.txt'], brief=B('P2-339564-abelianisation-proof.md'), prior='HOLD (possible Williams-coauthored successor; unverified)', accepted_credit=0),
  dict(id='P3', mathdb_id=337963, kind='proof', source='arXiv:1712.05883v1 Conjecture 49',
       quantifiers='for every M exists D0: every linear 2-tree with diam>=D0 has max resistance >=M (explicit: >=(diam-2)/6)',
       mechanism='hub-switch 3-edge cuts + Nash-Williams; hub walk bounds diameter',
       decisive_calculation='exhaustive m<=14 (8190) + 300 random: cut lemma, diam<=s+2, exact R>=ceil(s/2)/3, 0 failures',
       certificate_size='~1 page combinatorial proof', formal_dependencies='Nash-Williams inequality / Dirichlet principle; normal form of linear 2-trees',
       runs=['runs/l2t_check.exh14.r1.txt', 'runs/l2t_check.rand300.r1.txt'], brief=B('P3-337963-linear-2-tree-resistance-proof.md'),
       prior='HOLD; source lacks explicit linear 2-tree definition (scope)', accepted_credit=0)],
 retained_not_qualified=[
  dict(id='R1', mathdb_id=339455, kind='proof (routine adaptation)', source='arXiv:1806.02399v1 Conjecture 3.18',
       objection='explicit classical bridge (Taylor 1981 switching connectivity) + one-line Lipschitz lemma; likely prior interpolation literature',
       runs=['runs/tree_nu.r1.txt (vacuous: spread<=1)'], brief=B('R1-339455-tree-matching-interpolation.md'), accepted_credit=0)])
json.dump(props, open(os.path.join(O, 'proposals.json'), 'w'), ensure_ascii=False, indent=1)
# flat bindings (actual originals, no copies, no recursive historical trees)
fb = []
def add(role, p):
    h, n = sha(p); fb.append(dict(role=role, original=p, sha256=h, size=n))
for f in ['DECISION.md', 'queue.json', 'reserved-ids.json', 'coverage-delta.json', 'bindings.json', 'manifest.json', 'verification-receipt.json']:
    add('intake-r479-payload', os.path.join(INT, f))
add('intake-r479-verifier-hash-only-not-run', os.path.join(INT, 'verify.py'))
add('r301-manifest', os.path.join(CORP, 'manifest.json'))
m = json.load(open(os.path.join(CORP, 'manifest.json')))
for f in m['files']:
    if f['path'].startswith('corpus/'): add('r301-corpus-chunk', os.path.join(CORP, f['path']))
for f in m['frozen_inputs']: add('r301-frozen-input', os.path.join(CORP, f['path']))
for f in ['accepted-exclusions.json', 'historical-dispositions.json']: add('r304-exclusions', os.path.join(L, 'root-mathdb-accepted-exclusions-r304', f))
for f in ['DECISION.md', 'disposition.json']: add('r363-decision', os.path.join(L, 'root-mathdb-cayley-review-intake-r363', f))
add('helper-guard', os.path.join(L, 'sol-edge-irregulator-manuscript-packet-r1', 'packet', 'helper_guard.py'))
json.dump(dict(note='Flat references to actual originals; hashes frozen before scientific reading (see work/intake-prefreeze.txt, work/exclusions-prefreeze.txt). Intake 193 original/copy bindings and 199-file manifest verified by scripts/check_intake.py (runs/check_intake.r1.txt); not expanded here.',
               intake_binding_check=dict(bindings=193, failures=0, manifest_listed=199, manifest_mismatch=0), bindings=fb),
          open(os.path.join(O, 'bindings.json'), 'w'), ensure_ascii=False, indent=1)
from collections import Counter
print(json.dumps(dict(dispositions=len(disp), counts=Counter(d['disposition'] for d in disp), retained=len(ret), bindings=len(fb)), default=str))
