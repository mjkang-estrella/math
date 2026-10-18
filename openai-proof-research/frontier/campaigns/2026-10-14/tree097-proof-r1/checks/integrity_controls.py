#!/usr/bin/env python3
"""MIT. Copied mutation controls for the review verifier.

Usage: python3 -B integrity_controls.py --packet DIR --anchor HEX --workdir /var/tmp/...
Every mutation is applied to a fresh disposable copy under --workdir; the
original packet is never written. A reseal control rewrites a copy's manifest
to match a modified payload and confirms the old external anchor rejects it.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

def run(verifier, root, anchor):
    r = subprocess.run([sys.executable, '-B', str(verifier), '--root', str(root),
                        '--expected-manifest-sha256', anchor], capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', type=Path, required=True)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--workdir', type=Path, required=True)
    a = ap.parse_args()
    src = a.packet.resolve(); work = a.workdir.resolve()
    if work == src or src in work.parents: sys.exit('workdir must be outside the packet')
    work.mkdir(parents=True, exist_ok=True)
    verifier = src / 'verify.py'
    pick = 'report.md'

    made = []
    def fresh(tag):
        t = Path(tempfile.mkdtemp(prefix='t97ctl-' + tag + '-', dir=work)); made.append(t)
        d = t / 'pkt'
        shutil.copytree(src, d, symlinks=True)
        return d

    def reseal(d):
        m = json.loads((d / 'MANIFEST.json').read_text())
        for e in m['files']:
            b = (d / e['path']).read_bytes()
            e['bytes'] = len(b); e['sha256'] = hashlib.sha256(b).hexdigest()
        (d / 'MANIFEST.json').write_text(json.dumps(m, indent=1, sort_keys=True) + '\n')

    controls = []
    def ctl(name, mutate, expect_pass=False, anchor=None):
        d = fresh(name)
        if mutate: mutate(d)
        rc, out = run(verifier, d, anchor or a.anchor)
        ok = (rc == 0) == expect_pass
        controls.append({'control': name, 'expected': 'PASS' if expect_pass else 'FAIL',
                         'observed': 'PASS' if rc == 0 else 'FAIL', 'ok': ok, 'message': out[-160:]})

    ctl('positive', None, expect_pass=True)
    ctl('wrong-anchor', None, anchor='0' * 64)
    ctl('malformed-anchor', None, anchor='xyz')
    ctl('modified-payload', lambda d: (d / pick).write_text((d / pick).read_text() + 'x'))
    ctl('modified-payload-resealed', lambda d: ((d / pick).write_text((d / pick).read_text() + 'x'), reseal(d)))
    ctl('missing-file', lambda d: (d / pick).unlink())
    ctl('extra-file', lambda d: (d / 'extra.md').write_text('x'))
    ctl('extra-empty-dir', lambda d: (d / 'emptydir').mkdir())
    ctl('nested-manifest', lambda d: (d / 'checks' / 'MANIFEST.json').write_text('{}'))
    ctl('payload-symlink', lambda d: ((d / pick).unlink(), os.symlink('rederivation.md', d / pick)))
    ctl('dir-symlink', lambda d: os.symlink('checks', d / 'checks2'))
    ctl('hardlink', lambda d: os.link(d / pick, d.parent / 'hl'))
    ctl('fifo', lambda d: os.mkfifo(d / 'fifo'))
    def root_link(d):
        link = d.parent / 'rootlink'; os.symlink(d, link)
        rc, out = run(verifier, link, a.anchor)
        controls.append({'control': 'root-symlink', 'expected': 'FAIL',
                         'observed': 'PASS' if rc == 0 else 'FAIL', 'ok': rc != 0, 'message': out[-160:]})
    root_link(fresh('root-symlink'))
    for t in made:  # only the temporary copies this script created
        shutil.rmtree(t)
    res = {'all_ok': all(c['ok'] for c in controls), 'count': len(controls), 'controls': controls,
           'scope': 'Integrity of the verifier on disposable copies; not mathematics.'}
    print(json.dumps(res, indent=1))
    sys.exit(0 if res['all_ok'] else 1)

if __name__ == '__main__':
    main()
