"""Bind every checkpointed slice to its retained certificate domain and hash."""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import pathlib

H = pathlib.Path(__file__).resolve().parent

def main():
    stages = {}
    seen = {}
    for ledger in sorted(H.glob('search_*.json')):
        rows = json.loads(ledger.read_text())
        total = 0
        for key, row in rows.items():
            domains = set()
            for job in row['jobs']:
                path = pathlib.Path(job['file'])
                if str(path) not in seen:
                    raw = path.read_bytes()
                    seen[str(path)] = (json.loads(raw.splitlines()[0]), hashlib.sha256(raw).hexdigest())
                meta, digest = seen[str(path)]
                coefficients = [c for c, n in meta['groups'] for _ in range(n)]
                assert (meta['K'], coefficients, meta['qmin']) == (job['K'], job['coefs'], job['qmin']), (key, path)
                assert meta['scope'] == 'full' and meta['pin_digits'] <= meta['qmin']
                assert digest == job['sha256'], (key, path, 'changed checkpoint certificate')
                domain = job['K'], tuple(job['coefs']), job['qmin']
                assert domain not in domains, (key, domain)
                domains.add(domain)
                total += 1
            if row['status'] == 'COMPLETE_PENDING_CHECKS':
                assert len(domains) == row['slice_count'], key
        stages[ledger.name] = {'configurations': len(rows), 'retained_slice_references': total,
                              'statuses': dict(collections.Counter(r['status'] for r in rows.values()))}
    result = {'result': 'PASS', 'stages': stages, 'unique_checkpoint_certificates': len(seen)}
    (H / 'slice_domain_audit.json').write_text(json.dumps(result, indent=1) + '\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
