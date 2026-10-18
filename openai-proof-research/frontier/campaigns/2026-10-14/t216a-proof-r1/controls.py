#!/usr/bin/env python3
# MIT. Mutation controls run only on copies in a fresh /var/tmp directory; this packet is never written.
import json, os, shutil, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode = True
from verify import verify

root = Path(__file__).absolute().parent
anchor = sys.argv[1] if len(sys.argv) == 2 else ''
verify(root, anchor)
manifest = json.loads((root / 'manifest.json').read_text())
work = Path(tempfile.mkdtemp(prefix='t216a-proof-r1-controls.', dir='/var/tmp'))


def clone(name):
    d = work / name / 't216a-proof-r1'
    d.mkdir(parents=True)
    for x in manifest['directories']:
        (d / x).mkdir(parents=True, exist_ok=True)
    for x in list(manifest['files']) + ['manifest.json']:
        (d / x).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / x, d / x)
    return d


results = []
try:
    verify(clone('positive'), anchor)
    results.append('positive copied packet accepted')
    cases = ['wrong-anchor', 'short-anchor', 'changed-file', 'missing-file', 'extra-file',
             'extra-empty-directory', 'payload-symlink', 'directory-symlink', 'root-symlink',
             'ancestor-symlink', 'hardlinked-payload', 'fifo-payload', 'hardlinked-manifest',
             'changed-manifest', 'manifest-symlink']
    for name in cases:
        d = clone(name)
        a = anchor
        p = d / 'review.md'
        if name == 'wrong-anchor':
            a = '0' * 64
        elif name == 'short-anchor':
            a = anchor[:63]
        elif name == 'changed-file':
            p.write_bytes(p.read_bytes() + b'\nmutation\n')
        elif name == 'missing-file':
            p.unlink()
        elif name == 'extra-file':
            (d / 'extra').write_text('mutation')
        elif name == 'extra-empty-directory':
            (d / 'extra-empty').mkdir()
        elif name == 'payload-symlink':
            p.unlink(); p.symlink_to(root / 'review.md')
        elif name == 'directory-symlink':
            (d / 'linked-dir').symlink_to(root, target_is_directory=True)
        elif name == 'root-symlink':
            link = work / 'root-link'; link.symlink_to(d, target_is_directory=True); d = link
        elif name == 'ancestor-symlink':
            link = work / 'ancestor-link'; link.symlink_to(d.parent, target_is_directory=True); d = link / d.name
        elif name == 'hardlinked-payload':
            os.link(p, work / 'payload-hardlink')
        elif name == 'fifo-payload':
            p.unlink(); os.mkfifo(p)
        elif name == 'hardlinked-manifest':
            os.link(d / 'manifest.json', work / 'manifest-hardlink')
        elif name == 'changed-manifest':
            (d / 'manifest.json').write_text('{}\n')
        elif name == 'manifest-symlink':
            m = d / 'manifest.json'; m.unlink(); m.symlink_to(root / 'manifest.json')
        try:
            verify(d, a)
        except Exception:
            results.append(name + ' rejected')
        else:
            raise AssertionError('accepted mutation ' + name)
finally:
    shutil.rmtree(work)
verify(root, anchor)
print(json.dumps({'integrity_only': True, 'controls': results}, indent=2))
