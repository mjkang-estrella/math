"""Offline scheduling metadata only: never infer difficulty or reviewed scope."""
import collections
import hashlib
import json
from pathlib import Path
import sys
from urllib.parse import urldefrag

D = Path(__file__).resolve().parent
S = D.parent / 'root-mathdb-corpus-reconciliation-r307'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def write(name, value):
    (D / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

def inputs():
    original = S / 'manifest.json'
    bound = D / 'input-manifest.snapshot.json'
    if not bound.exists():
        before = sha(original)
        bound.write_bytes(original.read_bytes())
        assert sha(bound) == before == sha(original)
    expected = json.loads(bound.read_text())
    names = sorted(n for n in expected if n.startswith('frozen/mathdb-normalized-chunk-'))
    names += ['available-record-ids.json', 'reconciliation.json']
    for n in names:
        assert sha(S / n) == expected[n], n
    return names, expected

def build():
    names, expected = inputs()
    accepted = set(json.loads((S / 'reconciliation.json').read_text())['accepted_associated_ids_found'])
    queues = collections.defaultdict(list)
    sources = collections.defaultdict(list)
    status = collections.Counter()
    seen = set()
    with (D / 'coverage.jsonl').open('w') as out:
        for name in names:
            if not name.endswith('.jsonl'):
                continue
            with (S / name).open() as f:
                for line, raw in enumerate(f, 1):
                    r = json.loads(raw)
                    i = r['mathdb_id']
                    assert i not in seen
                    seen.add(i)
                    has_text = bool((r.get('statement') or '').strip())
                    label = r.get('statement_completeness')
                    queue = ('missing_statement' if not has_text else
                             'incomplete_statement' if label != 'full' else
                             'statement_screen')
                    queues[queue].append(i)
                    url = r.get('source_url')
                    if isinstance(url, str) and url:
                        # Same URL without page fragment is a retrieval-sharing hint,
                        # never proof that distinct source versions are equivalent.
                        sources[urldefrag(url)[0]].append(i)
                    status[str(r.get('status'))] += 1
                    row = {'mathdb_id': i, 'snapshot_file': name, 'line': line,
                           'queue': queue, 'inherited_status': r.get('status'),
                           'inherited_statement_completeness': label,
                           'accepted_scope_comparison_required': i in accepted,
                           'technical_review': 'not_reconciled',
                           'primary_body_review': 'not_reconciled',
                           'hypothesis_assignment': None}
                    out.write(json.dumps(row, sort_keys=True) + '\n')
    shards = []
    for queue, ids in sorted(queues.items()):
        ids.sort()
        for start in range(0, len(ids), 250):
            shards.append({'shard': f'{queue}-{start // 250 + 1:04d}',
                           'queue': queue, 'mathdb_ids': ids[start:start + 250],
                           'assignment': None, 'state': 'unassigned_snapshot_shard'})
    write('shards.json', shards)
    write('source-url-groups.json', dict(sources))
    write('input-bindings.json', [{'path': str(S / n), 'sha256': expected[n]} for n in names])
    write('summary.json', {'scope': 'Frozen partial multi-date corpus; not a live completeness claim',
                          'records': len(seen), 'queues': {k: len(v) for k, v in queues.items()},
                          'shards': len(shards), 'max_shard_records': 250,
                          'source_url_groups': len(sources),
                          'inherited_status_counts': dict(status),
                          'accepted_associated_ids_flagged': len(accepted & seen),
                          'technical_reviews_added': 0, 'primary_body_reviews_added': 0,
                          'hypotheses_dispatched': 0, 'credit_added': 0})
    for n in names:
        assert sha(S / n) == expected[n], n
    manifest = {str(p.relative_to(D)): sha(p) for p in sorted(D.rglob('*'))
                if p.is_file() and p.name not in {'manifest.json', 'verification-receipt.json'}}
    write('manifest.json', manifest)

def verify():
    # Separate process checks exact set partition and metadata against each source row.
    names, expected = inputs()
    manifest = json.loads((D / 'manifest.json').read_text())
    for name, digest in manifest.items():
        assert sha(D / name) == digest, name
    actual_files = {str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()
                    and p.name not in {'manifest.json', 'verification-receipt.json'}}
    assert actual_files == set(manifest)
    coverage = {}
    with (D / 'coverage.jsonl').open() as f:
        for raw in f:
            r = json.loads(raw)
            assert r['mathdb_id'] not in coverage
            coverage[r['mathdb_id']] = r
    reference_ids = json.loads((S / 'available-record-ids.json').read_text())
    assert set(coverage) == set(reference_ids)
    flat = []
    for shard in json.loads((D / 'shards.json').read_text()):
        assert 1 <= len(shard['mathdb_ids']) <= 250
        assert shard['assignment'] is None
        for i in shard['mathdb_ids']:
            assert coverage[i]['queue'] == shard['queue']
            flat.append(i)
    assert len(flat) == len(set(flat)) == len(coverage)
    assert set(flat) == set(coverage)
    records_checked = 0
    for name in names:
        if not name.endswith('.jsonl'):
            continue
        with (S / name).open() as f:
            for line, raw in enumerate(f, 1):
                r = json.loads(raw)
                c = coverage[r['mathdb_id']]
                assert (c['snapshot_file'], c['line']) == (name, line)
                assert c['technical_review'] == c['primary_body_review'] == 'not_reconciled'
                if not (r.get('statement') or '').strip():
                    assert c['queue'] == 'missing_statement'
                elif r.get('statement_completeness') == 'full':
                    assert c['queue'] == 'statement_screen'
                else:
                    assert c['queue'] == 'incomplete_statement'
                records_checked += 1
    assert records_checked == len(coverage)
    for n in names:
        assert sha(S / n) == expected[n], n
    write('verification-receipt.json', {'result': 'PASS', 'manifest_files': len(manifest),
          'immutable_inputs': len(names), 'source_rows_checked': records_checked,
          'partition_duplicates': 0, 'partition_omissions': 0,
          'technical_review_or_novelty_certified': False})
    print((D / 'verification-receipt.json').read_text())

if __name__ == '__main__':
    {'build': build, 'verify': verify}[sys.argv[1]]()
