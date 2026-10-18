#!/usr/bin/env python3
"""MIT. Copied-packet controls for this review's verifier; works only in a new /var/tmp directory."""
import argparse, hashlib, importlib.util, json, os, shutil, sys
from pathlib import Path


def main():
    p = argparse.ArgumentParser(); p.add_argument('--root', required=True); p.add_argument('--work', required=True)
    p.add_argument('--anchor', required=True); a = p.parse_args()
    root = Path(a.root).resolve(); work = Path(a.work).absolute()
    assert str(work).startswith('/var/tmp/') and not work.exists()
    work.mkdir(); results = []
    spec = importlib.util.spec_from_file_location('own_verifier', root / 'verify.py')
    v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)

    def run(name, mutate=None, anchor=None, expect=False, wrap=None):
        d = work / name; shutil.copytree(root, d, symlinks=True)
        if mutate:
            mutate(d)
        target = wrap(d) if wrap else d
        try:
            v.check(target, anchor or a.anchor); actual = 'PASS'
        except Exception as e:
            actual = 'REJECT: ' + str(e)
        results.append({'case': name, 'expected': 'accept' if expect else 'reject', 'actual': actual,
                        'as_expected': (actual == 'PASS') == expect})

    def touch(d, rel, data=b'changed\n'):
        f = d / rel; f.write_bytes(f.read_bytes() + data)

    def reseal(d):
        touch(d, 'review.md')
        m = json.loads((d / 'MANIFEST.json').read_text())
        for e in m['files']:
            b = (d / e['path']).read_bytes(); e['bytes'] = len(b); e['sha256'] = hashlib.sha256(b).hexdigest()
        (d / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')

    def payload_link(d):
        (d / 'review.md').unlink(); (d / 'review.md').symlink_to('README.md')

    def hardlink(d):
        (d / 'review.md').unlink(); os.link(d / 'README.md', d / 'review.md')

    def root_link(d):
        l = work / (d.name + '-link'); l.symlink_to(d, target_is_directory=True); return l

    def ancestor_link(d):
        l = work / (d.name + '-anc'); l.symlink_to(work, target_is_directory=True); return l / d.name

    try:
        run('positive_copy', expect=True)
        run('wrong_anchor', anchor='0' * 64)
        run('changed_review', lambda d: touch(d, 'review.md'))
        run('changed_private_comparator', lambda d: touch(d, next(e['path'] for e in json.loads((d / 'MANIFEST.json').read_text())['files'] if e['path'].startswith('private/'))))
        run('missing_payload', lambda d: (d / 'review.md').unlink())
        run('extra_file', lambda d: (d / 'extra.txt').write_text('x'))
        run('extra_empty_directory', lambda d: (d / 'extra-dir').mkdir())
        run('payload_symlink', payload_link)
        run('payload_hardlink', hardlink)
        run('fifo', lambda d: os.mkfifo(d / 'fifo'))
        run('nested_manifest', lambda d: (d / 'records' / 'MANIFEST.json').write_text('{}'))
        run('root_symlink', wrap=root_link)
        run('ancestor_symlink', wrap=ancestor_link)
        run('self_resealed_wrong_external_anchor', reseal)
    finally:
        shutil.rmtree(work)
    ok = all(r['as_expected'] for r in results)
    print(json.dumps({'status': 'PASS' if ok else 'FAIL', 'cases': results,
                      'scope': 'Copies of the sealed review directory under /var/tmp; identity only.'}, indent=2))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
