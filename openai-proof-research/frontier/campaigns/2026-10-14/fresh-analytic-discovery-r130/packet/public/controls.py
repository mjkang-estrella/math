#!/usr/bin/env python3
"""Copied integrity controls for analytic r130. Each case runs verify.py on a fresh copy under ROOT/work.
Explicit detached FINAL and REPORT anchors are required. Integrity only; no mathematical tests. MIT."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

PAYLOAD = 'public/screens.md'
EXPECT_ACCEPT = ('baseline', 'read-only-audit')

AUDIT_WRAPPER = r"""
import os, runpy, sys
target = sys.argv[1]
sys.argv = sys.argv[1:]
WRITE_FLAGS = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
DENY = {'os.remove', 'os.unlink', 'os.rename', 'os.replace', 'os.mkdir', 'os.rmdir', 'os.symlink', 'os.link',
        'os.chmod', 'os.chown', 'os.truncate', 'os.utime', 'shutil.rmtree', 'shutil.copyfile', 'subprocess.Popen'}
def hook(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(ch in mode for ch in 'wax+')) or (isinstance(flags, int) and flags & WRITE_FLAGS):
            raise RuntimeError('write denied by audit')
    if event in DENY:
        raise RuntimeError('mutation denied by audit')
sys.addaudithook(hook)
runpy.run_path(target, run_name='__main__')
"""


def h256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fingerprint(root):
    fp = {p.relative_to(root).as_posix(): h256(p) for p in sorted((root / 'packet').rglob('*'))
          if p.is_file() and not p.is_symlink()}
    fp['FINAL.json'] = h256(root / 'FINAL.json')
    fp['REPORT.md'] = h256(root / 'REPORT.md')
    return fp


def bump(p):
    p.write_bytes(p.read_bytes() + b'\n')


def register(pk):
    return json.loads((pk / 'private/upstream/canonical-register.json').read_text())


def reanchor(c, pk, payload):
    mp = pk / 'MANIFEST.json'
    m = json.loads(mp.read_text())
    for e in m['files']:
        if e['path'] == PAYLOAD:
            e['bytes'], e['sha256'] = payload.stat().st_size, h256(payload)
    mp.write_text(json.dumps(m))
    fpath = c / 'FINAL.json'
    f = json.loads(fpath.read_text())
    f['manifest_sha256'] = h256(mp)
    fpath.write_text(json.dumps(f))


def mutate(case, c):
    pk = c / 'packet'
    payload = pk / PAYLOAD
    if case == 'payload-edit':
        bump(payload)
    elif case == 'payload-delete':
        payload.unlink()
    elif case == 'extra-file':
        (pk / 'public/EXTRA.txt').write_text('x')
    elif case == 'extra-directory':
        (pk / 'public/extra').mkdir()
    elif case == 'payload-symlink':
        payload.unlink()
        payload.symlink_to(c / 'REPORT.md')
    elif case == 'directory-symlink':
        (pk / 'linked').symlink_to(pk / 'public', target_is_directory=True)
    elif case == 'payload-hardlink':
        os.link(payload, c / 'hardlink-outside-packet')
    elif case == 'report-edit':
        bump(c / 'REPORT.md')
    elif case == 'final-edit':
        bump(c / 'FINAL.json')
    elif case == 'manifest-edit':
        bump(pk / 'MANIFEST.json')
    elif case == 'reanchored-payload':
        bump(payload)
        reanchor(c, pk, payload)
    elif case == 'status-flip':
        fpath = c / 'FINAL.json'
        f = json.loads(fpath.read_text())
        f['status'], f['frozen'] = 'FROZEN', True
        fpath.write_text(json.dumps(f))
    elif case == 'canonical-metadata-edit':
        p = pk / 'private/upstream/canonical-register.json'
        z = json.loads(p.read_text())
        z[0]['canonical']['sha'] = 'f' * 40
        p.write_text(json.dumps(z))
    elif case == 'canonical-body-edit':
        bump(c / next(r['local'] for r in register(pk) if r['retained']))
    elif case == 'canonical-body-delete':
        (c / next(r['local'] for r in register(pk) if r['retained'])).unlink()
    elif case == 'literature-edit':
        bump(pk / 'private/literature/arxiv-2610.23853v1-receipt.md')
    elif case == 'round-flip':
        fpath = c / 'FINAL.json'
        f = json.loads(fpath.read_text())
        f['round'] = 'analytic-r129'
        fpath.write_text(json.dumps(f))
    elif case == 'tree-truncated':
        p = pk / 'private/context/sources__preprints-tree.json'
        z = json.loads(p.read_text())
        z['truncated'] = True
        p.write_text(json.dumps(z))
    elif case == 'history-edit':
        z = json.loads((pk / 'private/history/register.json').read_text())
        bump(c / z[0]['local'])
    elif case == 'context-edit':
        bump(pk / 'private/context/frontier__campaigns__2026-10-14__expanded-target-2026-10-17__fresh-analytic-r130-brief.txt')


CASES = ['baseline', 'missing-final', 'wrong-final', 'wrong-report', 'payload-edit', 'payload-delete',
         'extra-file', 'extra-directory', 'payload-symlink', 'directory-symlink', 'payload-hardlink',
         'report-edit', 'final-edit', 'manifest-edit', 'reanchored-payload', 'status-flip',
         'canonical-metadata-edit', 'canonical-body-edit', 'canonical-body-delete', 'tree-truncated',
         'history-edit', 'context-edit', 'literature-edit', 'round-flip', 'read-only-audit']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    root = a.root.resolve()
    before = fingerprint(root)
    (root / 'work').mkdir(exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix='controls-', dir=root / 'work') as td:
        for case in CASES:
            c = Path(td) / case
            c.mkdir()
            shutil.copytree(root / 'packet', c / 'packet', symlinks=True)
            shutil.copyfile(root / 'FINAL.json', c / 'FINAL.json')
            shutil.copyfile(root / 'REPORT.md', c / 'REPORT.md')
            fh = '0' * 64 if case == 'wrong-final' else a.final_sha256
            rh = '0' * 64 if case == 'wrong-report' else a.report_sha256
            mutate(case, c)
            verifier = c / 'packet/public/verify.py'
            args = ['--root', str(c), '--final-sha256', fh, '--report-sha256', rh]
            if case == 'missing-final':
                args = ['--root', str(c), '--report-sha256', rh]
            cmd = [sys.executable, '-B', str(verifier), *args]
            if case == 'read-only-audit':
                cmd = [sys.executable, '-B', '-c', AUDIT_WRAPPER, str(verifier), *args]
            r = subprocess.run(cmd, capture_output=True, text=True)
            accept = case in EXPECT_ACCEPT
            rows.append({'case': case, 'expected': 'accept' if accept else 'reject', 'exit': r.returncode,
                         'matched': (r.returncode == 0) == accept, 'stdout': r.stdout.strip(),
                         'stderr': r.stderr.strip()[-300:]})
            shutil.rmtree(c)
    unchanged = fingerprint(root) == before
    out = {'kind': 'INTEGRITY_CONTROLS_ONLY', 'mathematical_gate': False, 'detached_final': a.final_sha256,
           'detached_report': a.report_sha256, 'cases': rows, 'original_unchanged': unchanged,
           'all_expected': unchanged and all(x['matched'] for x in rows)}
    print(json.dumps(out, indent=2))
    return 0 if out['all_expected'] else 1


if __name__ == '__main__':
    sys.exit(main())
