#!/usr/bin/env python3
"""Disposable-copy controls for the independent verifier; original code, MIT."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

OWN = Path(__file__).resolve().parents[2]
REPO = OWN.parents[3]
SOURCE = OWN.parent / 'fresh-arithmetic-discovery-r93'
TREE = REPO / 'sources/preprints-tree.json'
ANCHORS = {
    'FINAL.json': '362dfe44e0db3abcddf9ce56f2a86f496e1e9c47297bf85c6e922847e760c479',
    'REPORT.md': '761a6e493e18f753c1f74902b3fade0a40ef12e34ec2dbb4474863c4d1b1dbe9',
    'packet/MANIFEST.json': '8464240a224199d82189adc4681d9e2a4e64a74495e22f46201ce37efdc782e5',
    'packet/public/FROZEN.md': 'ac626f4ab8d04589a8709854b9407f4577b72cdada161e6fe5f7943b7fa87572',
    'packet/public/proof.md': 'b05e2ea21ed2d31c1521e9ef32c38358c335c1beb6278459834adab9c864ebf2',
    'CONTROLS.json': '759b2467a1db4ae1ee793409e595ec88519d0e2b4c71cae5123675a158cd0f5e',
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    return json.loads(p.read_text())

def write(p, obj):
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def snapshot(root):
    records = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat()
        record = {'mode': stat.S_IMODE(s.st_mode), 'type': stat.S_IFMT(s.st_mode), 'nlink': s.st_nlink}
        if p.is_symlink():
            record['target'] = os.readlink(p)
        elif p.is_file():
            record.update(bytes=s.st_size, sha256=sha(p))
        records[str(p.relative_to(root))] = record
    return records

def invoke(root, anchor):
    run = subprocess.run([sys.executable, '-B', str(OWN / 'public/code/verify.py'), '--root', str(root), '--tree', str(TREE), '--final-sha256', anchor], capture_output=True, text=True, timeout=30)
    return {'returncode': run.returncode, 'stdout': run.stdout.strip(), 'stderr': run.stderr}

def reseal_copy(root):
    packet = root / 'packet'
    manifest = read(packet / 'MANIFEST.json')
    for name, rec in manifest['files'].items():
        p = packet / name
        rec.update(bytes=p.stat().st_size, sha256=sha(p))
    write(packet / 'MANIFEST.json', manifest)
    final = read(root / 'FINAL.json')
    final['manifest_sha256'] = sha(packet / 'MANIFEST.json')
    write(root / 'FINAL.json', final)
    return sha(root / 'FINAL.json')

def main():
    before = snapshot(SOURCE)
    tree_before = sha(TREE)
    for name, expected in ANCHORS.items():
        assert sha(SOURCE / name) == expected, name
    direct = invoke(SOURCE, ANCHORS['FINAL.json'])
    assert direct['returncode'] == 0, direct
    work = OWN / 'private/disposable'
    assert not work.exists()
    work.mkdir()
    cases = []
    names = ['baseline', 'wrong-anchor', 'changed-proof', 'missing-proof', 'extra-file', 'extra-directory', 'symlink', 'mode', 'hardlink', 'manifest', 'report', 'canonical-new-anchor', 'blob-new-anchor', 'freeze-new-anchor']
    try:
        for name in names:
            root = work / 'copy'
            shutil.copytree(SOURCE, root, symlinks=True)
            proof = root / 'packet/public/proof.md'
            anchor = ANCHORS['FINAL.json']
            if name == 'wrong-anchor':
                anchor = '0' * 64
            elif name == 'changed-proof':
                proof.write_bytes(proof.read_bytes() + b'\nCONTROL\n')
            elif name == 'missing-proof':
                proof.unlink()
            elif name == 'extra-file':
                (root / 'packet/EXTRA').write_text('control')
            elif name == 'extra-directory':
                (root / 'packet/EXTRA').mkdir()
            elif name == 'symlink':
                proof.unlink()
                proof.symlink_to('FROZEN.md')
            elif name == 'mode':
                proof.chmod(0o600)
            elif name == 'hardlink':
                os.link(proof, root / 'extra-hardlink')
            elif name == 'manifest':
                p = root / 'packet/MANIFEST.json'
                p.write_bytes(p.read_bytes() + b' ')
            elif name == 'report':
                p = root / 'REPORT.md'
                p.write_bytes(p.read_bytes() + b' ')
            elif name == 'canonical-new-anchor':
                p = root / 'packet/public/canonical.json'
                obj = read(p)
                obj[0]['canonical']['mode'] = '100755'
                write(p, obj)
                anchor = reseal_copy(root)
            elif name == 'blob-new-anchor':
                p = root / 'packet/public/canonical.json'
                obj = read(p)
                body = root / 'packet' / obj[0]['local']
                data = body.read_bytes()
                body.write_bytes(b'X' + data[1:])
                obj[0]['sha256'] = sha(body)
                write(p, obj)
                anchor = reseal_copy(root)
            elif name == 'freeze-new-anchor':
                p = root / 'packet/public/freeze.json'
                obj = read(p)
                obj['sha256'] = '0' * 64
                write(p, obj)
                anchor = reseal_copy(root)
            copied_before = snapshot(root)
            result = invoke(root, anchor)
            unchanged = copied_before == snapshot(root)
            expected = result['returncode'] == (0 if name == 'baseline' else 1)
            cases.append(dict(case=name, expected=expected, unchanged=unchanged, deliberate_new_test_anchor='new-anchor' in name, **result))
            assert unchanged and expected, cases[-1]
            shutil.rmtree(root)
    finally:
        shutil.rmtree(work)
    start = read(OWN / 'private/original-before.json')
    preserved = before == snapshot(SOURCE) == start['author_root']
    tree_preserved = tree_before == sha(TREE) == start['tree_sha256']
    assert preserved and tree_preserved
    write(OWN / 'private/integrity.json', {
        'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'detached_anchors': ANCHORS, 'direct_verification': direct, 'cases': cases,
        'whole_original_preserved': preserved, 'external_tree_preserved': tree_preserved,
        'all_expected': True, 'mathematical_gate': False,
        'limits': 'Own independently written verifier, no author program executed. 14 disposable-copy cases; three intentionally new test anchors. Full original paths/types/bytes/modes/link counts compared. No audit denial probes, hostile-runtime/race guarantee, or mathematical numerical test. Author manifest mode/root extras not sealed by author anchors.'})
    print(json.dumps({'cases': len(cases), 'all_expected': True, 'whole_original_preserved': preserved, 'external_tree_preserved': tree_preserved, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
