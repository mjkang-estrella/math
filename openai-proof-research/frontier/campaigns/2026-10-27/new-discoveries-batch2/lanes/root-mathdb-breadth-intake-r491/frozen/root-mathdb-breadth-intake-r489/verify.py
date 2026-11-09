from pathlib import Path
import hashlib, json, sys
from datetime import datetime, timezone

R = Path(__file__).resolve().parent
L = R.parent
C = R / 'frozen/sol-mathdb-primary-qualified-breadth-r486'
BASE = R / 'frozen/root-mathdb-breadth-intake-r487'
I = L / 'pi-mathdb-full-corpus-inventory-r301'

def read(p):
    return json.loads(p.read_text())

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def check(p, r):
    assert p.is_file(), str(p)
    assert p.stat().st_size == r.get('size', r.get('bytes')), str(p)
    assert sha(p) == r['sha256'], str(p)

def files(p, excluded):
    return {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()} - set(excluded)

def write(name, value):
    (R / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

bindings = read(R / 'bindings.json')
for r in bindings:
    check(Path(r['original']), r)
    check(Path(r['copy']), r)
cm = read(C / 'manifest.json')
excluded = {'manifest.json', 'final-receipt.json'}
assert set(cm['excluded_exact_paths']) == excluded
assert len(cm['files']) == 130
expected = {r['path'] for r in cm['files']}
assert len(expected) == len(cm['files']) and files(C, excluded) == expected
assert files(L / C.name, excluded) == expected
for r in cm['files']:
    check(C / r['path'], r)
refs = []
for name in ['flat-bindings.json', 'initial-bindings.json']:
    refs.extend(read(C / name))
for r in refs:
    check(Path(r['path']), r)
    if 'copy' in r:
        check(Path(r['copy']), r)
receipt = read(C / 'final-receipt.json')
assert receipt['status'] == 'PASS' and receipt['integrity_only'] is True
assert receipt['mathematics_pass'] is False and receipt['novelty_pass'] is False
assert receipt['accepted_credit'] == 0 and receipt['manifest_sha256'] == sha(C / 'manifest.json')
im = read(R / 'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')
assert im == read(I / 'manifest.json')
chunks = [r for r in im['files'] if r['path'].startswith('corpus/')]
assert len(chunks) == 20 and len(im['frozen_inputs']) == 8
for r in chunks + im['frozen_inputs']:
    check(I / r['path'], r)
coverage = read(BASE / 'coverage-delta.json')
assert len(coverage) == 3433
assignment = read(R / 'frozen/root-mathdb-breadth-intake-r485/reserved-ids.json')['ids']
rows = read(C / 'dispositions.json')
ids = {str(r['mathdb_id']) for r in rows}
assert len(ids) == len(rows) == 50 and ids == set(map(str, assignment))
assert not ids & set(coverage)
found = {}
for entry in chunks:
    p = I / entry['path']
    with p.open() as f:
        for line, s in enumerate(f, 1):
            record = json.loads(s)
            n = str(record['mathdb_id'])
            if n in ids:
                assert n not in found
                found[n] = (p, line, record)
assert set(found) == ids
for row in rows:
    p, line, record = found[str(row['mathdb_id'])]
    assert row['literal_statement'] == record['statement']
    assert row['original_chunk'] == str(p) and row['original_line'] == line
    assert row['statement_utf8_sha256'] == hashlib.sha256(record['statement'].encode()).hexdigest()
    canonical = json.dumps(record, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()
    assert row['canonical_record_sha256'] == hashlib.sha256(canonical).hexdigest()
    assert row['accepted_credit'] == 0
    coverage[str(row['mathdb_id'])] = {
        'disposition': row['disposition'],
        'report': C.name + '/dispositions.json',
        'record_statement_review': 'delegate_reported_complete',
        'evidence_level_reported': {k: row[k] for k in ('source_evidence_level','proof_evidence_level','prior_evidence_level','successor_evidence_level','current_registry')},
        'source_scope_cleared': False, 'prior_cleared': False, 'accepted_credit': 0,
        'proof_dependency_scope_reported': 'no_complete_dependency_audit',
        'scope_discipline_limit': 'Selected primary/proof passages plus one whole six-page primary body; dependencies and current registry remain unreviewed. Finite permutation recurrence checks are diagnostic only. Root integrity reconciliation only.'
    }
assert read(C / 'proposals.json')['qualified_briefs'] == [] and read(C / 'proposals.json')['accepted_credit'] == 0 and len(coverage) == 3483
held_sol = read(BASE / 'reserved-ids.json')['ids']
held_claude = read(R / 'frozen/root-mathdb-breadth-intake-r479/reserved-ids.json')['ids']
held = held_sol + held_claude
assert len(held) == len(set(held)) == 100 and not set(map(str, held)) & set(coverage)
queue = [json.loads(s) for s in (R / 'frozen/root-mathdb-breadth-intake-r415/routing-queue.jsonl').read_text().splitlines()]
seen = set(coverage) | set(map(str, held)) | {'372627', '372628', '368940', '404067', '364119'}
selected = []
for row in queue:
    n = str(row['mathdb_id'])
    if n in seen or row['status'] != 'open' or row['statement_completeness'] != 'full':
        continue
    selected.append(row)
    seen.add(n)
    if len(selected) == 50:
        break
assert len(selected) == 50
reservation = {'ids': [r['mathdb_id'] for r in selected], 'lane': 'sol-mathdb-primary-qualified-breadth-r490', 'status': 'reserved_not_reviewed', 'other_active_reservations': held}
outputs = {'coverage-delta.json': coverage, 'queue.json': selected, 'reserved-ids.json': reservation, 'adjudications.json': read(BASE / 'adjudications.json')}
own_excluded = {'manifest.json', 'verification-receipt.json'}
if sys.argv[1:] == ['build']:
    for name, value in outputs.items():
        write(name, value)
    write('manifest.json', {'files': [{'path': s, 'sha256': sha(R / s), 'size': (R / s).stat().st_size} for s in sorted(files(R, own_excluded))], 'excluded_exact_paths': sorted(own_excluded)})
elif sys.argv[1:] == ['verify']:
    for name, value in outputs.items():
        assert read(R / name) == value
    own = read(R / 'manifest.json')['files']
    assert files(R, own_excluded) == {r['path'] for r in own}
    for r in own:
        check(R / r['path'], r)
    write('verification-receipt.json', {'status': 'PASS', 'utc': datetime.now(timezone.utc).isoformat(), 'root_bindings': len(bindings), 'child_payloads': len(cm['files']), 'flat_reference_entries': len(refs), 'corpus_chunks': 20, 'inventory_frozen_inputs': 8, 'reported_statement_reviews': len(coverage), 'new_reservations': 50, 'other_reserved': 100, 'independent_math_replay': False, 'accepted_counts': [9, 39, 40]})
else:
    raise SystemExit('use build or verify')
print('PASS', sys.argv[1], len(coverage), 'reported reviews', len(refs), 'reference entries')
