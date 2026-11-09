"""Discard depth-three candidates that did not obtain independent F acceptance.

The original deep certificate and the full failed replay record remain intact.
Only M+F-passing depth-three candidates are retained as proof certificates.
"""
import sys
sys.dont_write_bytecode = True
import collections
import hashlib
import json
import pathlib

H = pathlib.Path(__file__).resolve().parent

def main():
    path = H / 'checks5.json'
    data = json.loads(path.read_text())
    removed_path = H / 'discarded_ablation_candidates.json'
    removed = json.loads(removed_path.read_text()) if removed_path.exists() else []
    with (H / 'checks5_journal.jsonl').open('a') as log:
        for original, record in data['files'].items():
            ab = record.get('downgrade', {})
            if 'file' not in ab or ab.get('F', {}).get('result') == 'PASS':
                continue
            candidate = pathlib.Path(ab.pop('file'))
            assert candidate.parent == H / 'k3_certs'
            assert hashlib.sha256(candidate.read_bytes()).hexdigest() == ab['M']['sha256']
            candidate.unlink()
            ab.update(result='FAIL', failure_stage='independent_F',
                      removed_candidate=str(candidate))
            removed.append({'original': original, 'candidate': str(candidate), 'F': ab.get('F')})
            log.write(json.dumps({'file': original, 'record': record}, separators=(',', ':')) + '\n')
            log.flush()
    data['downgrades'] = dict(collections.Counter(r['downgrade'].get('result', 'PASS')
        for r in data['files'].values() if 'downgrade' in r))
    temp = path.with_suffix('.json.tmp')
    temp.write_text(json.dumps(data, indent=1) + '\n')
    temp.replace(path)
    removed_path.write_text(json.dumps(removed, indent=1) + '\n')
    print(json.dumps({'discarded_unvalidated_candidates': len(removed)}))

if __name__ == '__main__':
    main()
