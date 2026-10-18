#!/usr/bin/env python3
# MIT. Positive, wrong-anchor and mutation controls. All writes go to a fresh
# directory under /var/tmp; the sealed packet given as ROOT is only read.
import importlib.util, json, os, shutil, sys, tempfile
from pathlib import Path

sys.dont_write_bytecode = True
if len(sys.argv) != 3:
    raise SystemExit('usage: controls.py ROOT EXTERNAL_MANIFEST_SHA256')
root = Path(sys.argv[1]).absolute()
anchor = sys.argv[2]
spec = importlib.util.spec_from_file_location('review_verify', root / 'verify.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
v.verify(root, anchor)
manifest = json.loads((root / 'manifest.json').read_text())
work = Path(tempfile.mkdtemp(prefix='t216a-contrib-controls-', dir='/var/tmp'))


def clone(name):
    d = work / name
    d.mkdir()
    for x in manifest['directories']:
        (d / x).mkdir(parents=True, exist_ok=True)
    for x in list(manifest['files']) + ['manifest.json']:
        (d / x).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / x, d / x)
    return d


results = []
try:
    d = clone('positive')
    v.verify(d, anchor)
    results.append('positive copied packet accepted')
    cases = ['wrong-anchor', 'truncated-anchor', 'changed-file', 'missing-file', 'extra-file',
             'extra-empty-directory', 'payload-symlink', 'directory-symlink', 'root-symlink',
             'ancestor-symlink', 'hardlinked-payload', 'fifo-payload', 'hardlinked-manifest',
             'changed-manifest', 'reinventoried-after-change']
    for name in cases:
        d = clone(name)
        a = anchor
        p = d / 'review.md'
        if name == 'wrong-anchor':
            a = '0' * 64
        elif name == 'truncated-anchor':
            a = anchor[:-1]
        elif name == 'changed-file':
            p.write_bytes(p.read_bytes() + b'\nmutation\n')
        elif name == 'missing-file':
            p.unlink()
        elif name == 'extra-file':
            (d / 'extra.txt').write_text('mutation')
        elif name == 'extra-empty-directory':
            (d / 'extra-empty').mkdir()
        elif name == 'payload-symlink':
            p.unlink()
            p.symlink_to(root / 'review.md')
        elif name == 'directory-symlink':
            (d / 'linked-dir').symlink_to(work / 'positive', target_is_directory=True)
        elif name == 'root-symlink':
            link = work / 'root-link'
            link.symlink_to(d, target_is_directory=True)
            d = link
        elif name == 'ancestor-symlink':
            link = work / 'ancestor-link'
            link.symlink_to(d.parent, target_is_directory=True)
            d = link / d.name
        elif name == 'hardlinked-payload':
            os.link(p, work / 'payload-hardlink')
        elif name == 'fifo-payload':
            p.unlink()
            os.mkfifo(p)
        elif name == 'hardlinked-manifest':
            os.link(d / 'manifest.json', work / 'manifest-hardlink')
        elif name == 'changed-manifest':
            (d / 'manifest.json').write_text('{}\n')
        elif name == 'reinventoried-after-change':
            p.write_bytes(p.read_bytes() + b'\nmutation\n')
            inv = v.inventory(d)
            (d / 'manifest.json').write_text(json.dumps(inv, sort_keys=True, indent=2) + '\n')
        try:
            v.verify(d, a)
        except Exception:
            results.append(name + ' rejected')
        else:
            raise AssertionError('accepted mutation ' + name)
finally:
    shutil.rmtree(work)
print(json.dumps({'integrity_only': True, 'controls': results}, indent=2))
