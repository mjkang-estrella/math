"""Sparse, evidence-labelled coverage update; no mathematical verdicts inferred."""
import collections
import hashlib
import json
from pathlib import Path
import sys

D = Path(__file__).resolve().parent
L = D.parent
INPUTS = {
    'shards': ('root-mathdb-coverage-queue-r309', 'shards.json', 'manifest.json'),
    'coverage': ('root-mathdb-inventory-intake-r311', 'reported-record-coverage.json', 'ROOT-MANIFEST.json'),
    'dispatch': ('root-mathdb-inventory-intake-r311', 'dispatch-reservations.json', 'ROOT-MANIFEST.json'),
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n, x):
    (D / n).write_text(json.dumps(x, indent=2, sort_keys=True) + '\n')
def load_inputs():
    bindings, values = [], {}
    for key, (lane, filename, manifest_name) in INPUTS.items():
        p = L / lane / filename
        manifest = json.loads((L / lane / manifest_name).read_text())
        digest = manifest[filename]
        assert sha(p) == digest
        bindings.append({'name': key, 'path': str(p), 'sha256': digest})
        values[key] = json.loads(p.read_text())
        assert sha(p) == digest
    return bindings, values

if sys.argv[1] == 'build':
    bindings, data = load_inputs()
    reviewed = data['coverage']['records']
    assignments = collections.defaultdict(list)
    for task in data['dispatch']:
        for i in task['ids']:
            assignments[str(i)].append({'lane': task['lane'], 'purpose': task['purpose']})
    changes = {}
    for i in sorted(set(reviewed) | set(assignments), key=int):
        changes[i] = {'record_statement_review': 'reported_complete' if i in reviewed else 'not_yet_reported',
                      'record_review_evidence': reviewed.get(i, []),
                      'primary_body_review': 'reported_partial' if int(i) == 371202 else 'not_reported',
                      'assignments': assignments.get(i, []),
                      'source_scope_cleared': False, 'prior_cleared': False,
                      'accepted_credit': 0}
    # 'reported_complete' means completion of that review activity, not that
    # the cached statement was ungarbled, authoritative, or mathematically correct.
    shard_state = []
    universe = set()
    for shard in data['shards']:
        ids = set(map(str, shard['mathdb_ids']))
        assert not (universe & ids)
        universe |= ids
        pending = ids - set(reviewed)
        assigned_pending = pending & set(assignments)
        shard_state.append({'shard': shard['shard'], 'queue': shard['queue'], 'total': len(ids),
                            'reported_record_reviews': len(ids & set(reviewed)),
                            'assigned_without_report': len(assigned_pending),
                            'unassigned_without_report': len(pending - assigned_pending),
                            'unassigned_ids': sorted(map(int, pending - assigned_pending))})
    assert set(changes) <= universe
    write('coverage-delta.json', changes)
    write('shard-state.json', shard_state)
    write('bindings.json', bindings)
    write('summary.json', {'snapshot_ids': len(universe), 'reported_statement_review_ids': len(reviewed),
                          'assigned_new_breadth_ids': len(set(assignments) - set(reviewed)),
                          'unassigned_without_statement_review_report': len(universe - set(reviewed) - set(assignments)),
                          'hypothesis_assignments': [x for x in data['dispatch'] if len(x['ids']) == 1],
                          'complete_primary_body_reviews_reported': 0,
                          'statement_review_is_source_or_novelty_clearance': False, 'credit_added': 0})
    write('manifest.json', {p.name: sha(p) for p in D.iterdir() if p.is_file()
                           and p.name not in {'manifest.json', 'verification-receipt.json'}})
else:
    bindings, data = load_inputs()
    assert bindings == json.loads((D / 'bindings.json').read_text())
    manifest = json.loads((D / 'manifest.json').read_text())
    for n, digest in manifest.items():
        assert sha(D / n) == digest
    summary = json.loads((D / 'summary.json').read_text())
    states = json.loads((D / 'shard-state.json').read_text())
    assert sum(s['total'] for s in states) == summary['snapshot_ids'] == 95675
    assert sum(s['reported_record_reviews'] for s in states) == summary['reported_statement_review_ids'] == 83
    assert sum(s['assigned_without_report'] for s in states) == summary['assigned_new_breadth_ids'] == 50
    pending = [i for s in states for i in s['unassigned_ids']]
    assert len(pending) == len(set(pending)) == summary['unassigned_without_statement_review_report']
    assert len(pending) + 83 + 50 == 95675
    write('verification-receipt.json', {'result': 'PASS', 'manifest_files': len(manifest),
          'bound_inputs': len(bindings), 'shards': len(states),
          'partition_exhaustive_disjoint': True, 'mathematical_review_performed': False})
    print((D / 'summary.json').read_text())
