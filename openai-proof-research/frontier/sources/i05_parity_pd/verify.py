#!/usr/bin/env python3
"""Read-only byte-integrity check; not a mathematical proof verifier."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify():
    manifest = json.loads((HERE / 'manifest.json').read_text())
    tree = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
    blobs = {r['path']: r['sha'] for r in tree['tree']}
    errors, changed = [], []
    if tree['truncated']:
        errors.append('complete tree unexpectedly truncated')
    for r in manifest['upstream']:
        data = (HERE / r['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if sha(data) != r['sha256'] or blob != r['git_blob'] or blob != blobs.get(r['path']):
            errors.append(r['path'])
        if manifest['pin'] not in r['url']:
            errors.append('unpinned URL: ' + r['url'])
    downloaded = 0
    for r in manifest['external']:
        if 'error' in r:
            continue
        downloaded += 1
        if sha((HERE / r['local']).read_bytes()) != r['sha256']:
            errors.append(r['local'])
    for name, expected in manifest['inputs'].items():
        actual = sha((ROOT / name).read_bytes())
        if actual != expected:
            changed.append({'path': name, 'recorded': expected, 'current': actual})
    protected = [r for r in changed if r['path'].startswith(('frontier/findings/R006',
                 'frontier/iterations/i03-arithmetic-progressions',
                 'frontier/reviews/i03-arithmetic-progressions'))]
    result = {'pinned_files_checked': len(manifest['upstream']),
              'external_download_hashes_checked': downloaded,
              'immutable_errors': errors, 'mutable_input_changes': changed,
              'R006_input_changes': protected,
              'passed': not errors and not protected}
    return result


if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['passed'] else 1)
