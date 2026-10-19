#!/usr/bin/env python3
"""MIT. Verifier rejection controls on small temporary fixtures, within private/."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(b):
    return hashlib.sha256(b).hexdigest()


def run():
    root = Path(__file__).absolute().parent
    (root/'private').mkdir(exist_ok=True)
    outcomes = {}
    with tempfile.TemporaryDirectory(prefix='control-', dir=root/'private') as temp:
        base = Path(temp)
        fixture = base/'fixture'
        fixture.mkdir()
        shutil.copyfile(root/'verify.py', fixture/'verify.py')
        (fixture/'source-receipts.json').write_text('[]\n')
        (fixture/'primary-receipts.json').write_text('[]\n')
        (fixture/'payload.txt').write_text('Original fixture only.\n')
        records = []
        for f in sorted(fixture.iterdir()):
            b = f.read_bytes()
            records.append({'path': f.name, 'sha256': sha(b), 'bytes': len(b)})
        manifest = {'schema': 'r73-integrity-v1',
                    'pinned_revision': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                    'public_files': records,
                    'canonical_tree': {'sha256': 'f'*64}}
        raw = (json.dumps(manifest, indent=2)+'\n').encode()
        (fixture/'manifest.json').write_bytes(raw)
        anchor = sha(raw)
        (fixture/'manifest.sha256').write_text(anchor+'\n')

        def execute(folder, extra):
            r = subprocess.run([sys.executable, '-B', str(folder/'verify.py'), *extra],
                               capture_output=True, text=True)
            return r.returncode

        assert execute(fixture, ['--expected-manifest-sha256', anchor]) == 0
        outcomes['baseline_fixture'] = 'accepted'
        assert execute(fixture, []) != 0
        outcomes['missing_external_anchor'] = 'rejected'
        assert execute(fixture, ['--expected-manifest-sha256', '0'*64]) != 0
        outcomes['wrong_external_anchor'] = 'rejected'
        for name in ('changed_payload', 'missing_payload', 'extra_public_file',
                     'symlink_payload', 'changed_manifest', 'self_resealed_manifest',
                     'wrong_sidecar', 'wrong_canonical_tree'):
            case = base/name
            shutil.copytree(fixture, case)
            extra = ['--expected-manifest-sha256', anchor]
            if name == 'changed_payload':
                (case/'payload.txt').write_text('changed\n')
            elif name == 'missing_payload':
                (case/'payload.txt').unlink()
            elif name == 'extra_public_file':
                (case/'extra.txt').write_text('extra\n')
            elif name == 'symlink_payload':
                (case/'payload.txt').unlink()
                (case/'payload.txt').symlink_to(fixture/'payload.txt')
            elif name in ('changed_manifest', 'self_resealed_manifest'):
                changed = raw+b' '
                (case/'manifest.json').write_bytes(changed)
                if name == 'self_resealed_manifest':
                    (case/'manifest.sha256').write_text(sha(changed)+'\n')
            elif name == 'wrong_sidecar':
                (case/'manifest.sha256').write_text('0'*64+'\n')
            elif name == 'wrong_canonical_tree':
                bad_tree = base/'bad-tree.json'
                bad_tree.write_text('{"tree": [], "truncated": true}\n')
                extra += ['--canonical-tree', str(bad_tree)]
            assert execute(case, extra) != 0, name
            outcomes[name] = 'rejected'
    return {'scope': 'integrity verifier fixtures only, not mathematical validation',
            'outcomes': outcomes, 'temporary_fixtures_removed': True}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
