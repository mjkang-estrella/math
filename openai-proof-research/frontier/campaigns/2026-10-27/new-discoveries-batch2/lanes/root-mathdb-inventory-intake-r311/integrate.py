import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

D = Path(__file__).resolve().parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n, x):
    (D / n).write_text(json.dumps(x, indent=2, sort_keys=True) + '\n')
def verify_bindings():
    for r in json.loads((D / 'bindings.json').read_text()):
        assert sha(Path(r['original'])) == sha(D / r['copy']) == r['sha256']

if sys.argv[1] == 'build':
    verify_bindings()
    records = collections.defaultdict(list)
    for subject, name in [('finite', 'finite/screening/dispositions.json'),
                          ('analysis', 'analysis/dispositions.json')]:
        data = json.loads((D / name).read_text())
        for r in data['dispositions']:
            records[r['mathdb_id']].append({'subject': subject, 'disposition': r['disposition'],
                'evidence': name, 'level': 'delegate_reported_record_statement_review'})
    selected = []
    with (D / 'tags/review-queue-top.jsonl').open() as f:
        for line in f:
            r = json.loads(line)
            if r['mathdb_id'] not in records and r.get('status') == 'open':
                selected.append(r['mathdb_id'])
                if len(selected) == 50:
                    break
    assert len(selected) == len(set(selected)) == 50
    write('reported-record-coverage.json', {'distinct_ids': len(records),
          'records': dict(records), 'overlap_ids': [i for i, r in records.items() if len(r) > 1],
          'completed_primary_body_reviews_reported': 0, 'partial_primary_body_review_ids': [371202]})
    write('next-breadth-ids.json', selected)
    p = D.parent / 'root-mathdb-hypothesis-intake-r306/intake.py'
    digest = sha(p)
    q = D / 'intake.snapshot.py'
    q.write_bytes(p.read_bytes())
    assert sha(q) == digest == sha(p)
    refs = json.loads((D / 'bindings.json').read_text())
    refs.append({'original': str(p), 'copy': q.name, 'sha256': digest})
    write('bindings.json', refs)
    spec = importlib.util.spec_from_file_location('frozen_intake', q)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    index_path = D.parent / 'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'
    # Reuse the immutable input already frozen and verified in r310.
    frozen_index = D.parent / 'root-first-thirty-preservation-r310/accepted-index.json'
    assert sha(index_path) == sha(frozen_index)
    index = json.loads(frozen_index.read_text())
    rows = json.loads((D / 'finite/intake-proposals.json').read_text())['proposals']
    rows += json.loads((D / 'analysis/proposals.json').read_text())['proposals']
    result = module.intake(index, rows)
    write('proposal-intake.json', result)
    write('dispatch-reservations.json', [
          {'lane': 'pi-fibonacci-minima-source-hypothesis-r312', 'ids': [371202], 'purpose': 'source qualification, then substantive attempt if justified'},
          {'lane': 'pi-weighted-clt-source-hypothesis-r313', 'ids': [368302], 'purpose': 'source qualification, then substantive attempt if justified'},
          {'lane': 'pi-mathdb-primary-first-breadth-r314', 'ids': selected, 'purpose': 'record-level screening and primary-body qualification'}])
    verify_bindings()
    write('ROOT-MANIFEST.json', {str(p.relative_to(D)): sha(p) for p in sorted(D.rglob('*'))
          if p.is_file() and str(p.relative_to(D)) not in {'ROOT-MANIFEST.json', 'ROOT-RECEIPT.json'}})
else:
    verify_bindings()
    manifest = json.loads((D / 'ROOT-MANIFEST.json').read_text())
    for n, h in manifest.items():
        assert sha(D / n) == h, n
    coverage = json.loads((D / 'reported-record-coverage.json').read_text())
    selected = json.loads((D / 'next-breadth-ids.json').read_text())
    assert len(selected) == len(set(selected)) == 50
    assert not (set(selected) & set(map(int, coverage['records'])))
    result = json.loads((D / 'proposal-intake.json').read_text())
    write('ROOT-RECEIPT.json', {'result': 'PASS', 'manifest_files': len(manifest),
          'reported_distinct_statement_reviews': coverage['distinct_ids'],
          'review_overlap_ids': coverage['overlap_ids'],
          'proposal_rows': result['proposal_rows'],
          'dispatch_ready_without_further_qualification': sum(r['dispatch'] == 'ready_for_orchestrator_selection' for r in result['proposals']),
          'reserved_new_breadth_ids': 50, 'credit_added': 0})
    print((D / 'ROOT-RECEIPT.json').read_text())
