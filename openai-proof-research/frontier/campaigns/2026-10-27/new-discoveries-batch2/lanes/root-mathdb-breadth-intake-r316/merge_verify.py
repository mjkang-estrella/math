import hashlib, json, sys
from pathlib import Path

L = Path(__file__).resolve().parent
B = L.parent
F = L/'frozen'
D = B/'pi-mathdb-primary-first-breadth-r314'

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def read(name):
    return json.loads((F/name).read_text())

def write(name, obj):
    (L/name).write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')

def check_inputs():
    bindings = json.loads((L/'bindings.json').read_text())
    for item in bindings:
        assert digest(Path(item['source'])) == item['sha256'], item['source']
        assert digest(L/item['copy']) == item['sha256'], item['copy']
    receipt = read('r314-receipt.json')
    assert receipt['pass'] is True
    for name, item in receipt['files'].items():
        assert digest(D/name) == item['sha256'], name
        assert (D/name).stat().st_size == item['bytes'], name
    chunks = read('r314-bindings.json')['chunk_sha256']
    for name, expected in chunks.items():
        assert digest(B/'pi-mathdb-full-corpus-inventory-r301/corpus'/name) == expected, name
    reserved = read('r311-reserved.json')
    rows = read('r314-dispositions.json')['dispositions']
    assert len(reserved) == len(set(reserved)) == len(rows) == 50
    assert sorted(r['id'] for r in rows) == sorted(reserved)
    old = read('r315-coverage.json')
    reviewed = {int(k) for k,v in old.items() if v['record_statement_review']=='reported_complete'}
    assert len(reviewed) == 83
    assert not reviewed.intersection(reserved)
    proposals = read('r314-proposals.json')['proposals']
    assert len(proposals) == 5
    assert {p['mathdb_id'] for p in proposals} <= set(reserved)
    return old, rows, {'frozen_input_pairs':len(bindings), 'delegate_receipt_hashes':len(receipt['files']), 'corpus_hashes':len(chunks), 'new_record_reports':50, 'prior_record_reports':83}

def build():
    old, rows, checks = check_inputs()
    for row in rows:
        entry = old[str(row['id'])]
        entry['record_statement_review'] = 'reported_complete'
        entry['record_review_evidence'].append({'disposition':row['disposition'], 'evidence':'frozen/r314-dispositions.json', 'level':'delegate_reported_record_statement_review', 'qualification':'technical conclusions not independently reviewed'})
        entry['assignments'] = [dict(a, lifecycle='completed_notification_and_terminal_thread_read') for a in entry['assignments']]
        entry['primary_body_review'] = 'reported_partial_section_read_no_retained_body_binding' if row['id']==350551 else 'not_reported'
        entry['source_scope_cleared'] = False
        entry['prior_cleared'] = False
        entry['accepted_credit'] = 0
    old['322922']['assignments'].append({'lane':'pi-rainbow-path-replication-hypothesis-r317','purpose':'single-hypothesis primary/successor qualification then bounded full-scope attempt','lifecycle':'launch_confirmed_running_not_live_status'})
    write('coverage-delta.json', old)
    write('summary.json', {'known_ids':95675,'record_statement_reviews_reported':133,'remaining_without_record_review_report':95542,'new_record_reports':50,'complete_primary_body_reviews_established':0,'partial_primary_body_reports':2,'primary_report_350551_retained_bytes_missing':True,'source_or_novelty_clearance_added':0,'new_acceptances':0,'accepted_total':39,'checks':checks,'qualification':'Coverage counts reported reading activity, not correctness, novelty, mathematical validation or acceptance.'})
    write('dispatch.json', {'allocation_checkpoint_not_live_status':True,'assigned':[{'lane':'pi-fibonacci-minima-source-hypothesis-r312','mathdb_id':371202},{'lane':'pi-weighted-clt-source-hypothesis-r313','mathdb_id':368302},{'lane':'pi-rainbow-path-replication-hypothesis-r317','mathdb_id':322922}],'completed':'pi-mathdb-primary-first-breadth-r314','next_free_slot_priority':'disjoint breadth with primary-body qualification; do not infer all five r314 proposals are tractable'})
    write('intake-qualifications.json', {
        'manifest':'r314 manifest files map paths to descriptions, not hashes. Its receipt separately records 10 payload hashes; root compares those fixed hashes.',
        'readiness_check':'r314 verify.py proposal readiness branch ends in or True: pass, so it proves no readiness property.',
        'primary_custody':'No retained primary body or primary retrieval/hash binding appears among the r314 payload files. Reported section reading is not independently established body custody.',
        'dedup':'Root verifies disjointness from 83 prior statement IDs only. The claim of zero exact historical-scope overlap is not established by the inspected verifier.',
        'chronology':'r314 reports generated/read dates 2026-11-02, while the authoritative terminal run completedAt is 2026-10-30T22:47:26.443Z. Report dates are not accepted as retrieval timestamps.',
        '350551':'Potential source-internal prior refutation, not a promoted new discovery; exact definitions and source comparison remain required.',
        'finite_evidence':'Finite coefficient guessing, numerical motion searches, or agreement of DP tables cannot establish universal induction, non-D-finiteness or rigidity.',
        'stale_labels':'Five abstract/record-level purported resolutions remain unverified exclusions.',
        'all_proposals':'All five unqualified. No automatic exclusion, novelty clearance, substantive credit or formal investment.'
    })
    manifest = {str(p.relative_to(L)):digest(p) for p in sorted(L.rglob('*')) if p.is_file() and p.relative_to(L).as_posix() not in ('manifest.json','verification-receipt.json')}
    write('manifest.json',manifest)
    print(json.dumps({'built':True,'checks':checks,'manifest_entries':len(manifest)}))

def verify():
    _, _, checks = check_inputs()
    manifest = json.loads((L/'manifest.json').read_text())
    actual = {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.relative_to(L).as_posix() not in ('manifest.json','verification-receipt.json')}
    assert actual == set(manifest)
    for name, expected in manifest.items():
        assert digest(L/name) == expected, name
    overlay = json.loads((L/'coverage-delta.json').read_text())
    assert sum(v['record_statement_review']=='reported_complete' for v in overlay.values()) == 133
    assert all(v['accepted_credit']==0 for v in overlay.values())
    assert all(not v['prior_cleared'] and not v['source_scope_cleared'] for v in overlay.values())
    result={'pass':True,'manifest_entries':len(manifest),'checks':checks,'scope':'Hash integrity, exact ID coverage and conservative gate states only; no mathematical, primary-custody, prior-art or acceptance validation.'}
    write('verification-receipt.json',result)
    print(json.dumps(result))

if __name__=='__main__':
    if sys.argv[1:] == ['build']:
        build()
    elif sys.argv[1:] == ['verify']:
        verify()
    else:
        raise SystemExit('use build or verify')
