#!/usr/bin/env python3
"""Copied integrity controls for analytic r128; explicit detached anchors required. No math tests. MIT."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

CASES = ['baseline', 'missing-final', 'wrong-final', 'wrong-report', 'payload-edit', 'payload-delete',
         'extra-file', 'extra-directory', 'payload-symlink', 'directory-symlink', 'payload-hardlink',
         'report-edit', 'final-edit', 'manifest-edit', 'reanchored-payload', 'canonical-edit',
         'canonical-body-edit', 'removed-body-reappears', 'tree-truncated', 'history-edit',
         'context-edit', 'read-only-audit']
ACCEPT = {'baseline', 'read-only-audit'}
PAYLOAD = 'public/screens.md'

AUDIT = """import sys,runpy,os
p=sys.argv[1];sys.argv=sys.argv[1:]
def audit(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):raise RuntimeError('write denied')
 if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.symlink','os.link','os.chmod','os.chown','os.truncate','shutil.rmtree','subprocess.Popen'}:raise RuntimeError('mutation denied')
sys.addaudithook(audit);runpy.run_path(p,run_name='__main__')
"""


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(r):
    s = {p.relative_to(r).as_posix(): sha(p) for p in sorted((r / 'packet').rglob('*')) if p.is_file()}
    s['FINAL.json'] = sha(r / 'FINAL.json')
    s['REPORT.md'] = sha(r / 'REPORT.md')
    return s


def append(p):
    p.write_bytes(p.read_bytes() + b'!')


def mutate(name, c):
    pk = c / 'packet'
    payload = pk / PAYLOAD
    if name == 'payload-edit':
        append(payload)
    elif name == 'payload-delete':
        payload.unlink()
    elif name == 'extra-file':
        (pk / 'EXTRA').write_text('extra')
    elif name == 'extra-directory':
        (pk / 'EXTRA').mkdir()
    elif name == 'payload-symlink':
        payload.unlink()
        payload.symlink_to(c / 'REPORT.md')
    elif name == 'directory-symlink':
        (pk / 'EXTRA').symlink_to(pk / 'public', target_is_directory=True)
    elif name == 'payload-hardlink':
        os.link(payload, c / 'outside-hardlink')
    elif name == 'report-edit':
        (c / 'REPORT.md').write_text('changed')
    elif name == 'final-edit':
        (c / 'FINAL.json').write_text('{}')
    elif name == 'manifest-edit':
        (pk / 'MANIFEST.json').write_text('{}')
    elif name == 'reanchored-payload':
        append(payload)
        mp = pk / 'MANIFEST.json'
        m = json.loads(mp.read_text())
        for e in m['files']:
            if e['path'] == PAYLOAD:
                e.update(bytes=payload.stat().st_size, sha256=sha(payload))
        mp.write_text(json.dumps(m))
        fp = c / 'FINAL.json'
        f = json.loads(fp.read_text())
        f['manifest_sha256'] = sha(mp)
        fp.write_text(json.dumps(f))
    elif name == 'canonical-edit':
        p = pk / 'private/upstream/canonical-register.json'
        z = json.loads(p.read_text())
        z[0]['canonical']['sha'] = '0' * 40
        p.write_text(json.dumps(z))
    elif name == 'canonical-body-edit':
        z = json.loads((pk / 'private/upstream/canonical-register.json').read_text())
        append(c / next(r['local'] for r in z if r['retained']))
    elif name == 'removed-body-reappears':
        z = json.loads((pk / 'private/upstream/canonical-register.json').read_text())
        p = c / next(r['local'] for r in z if not r['retained'])
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('reappeared')
    elif name == 'tree-truncated':
        p = pk / 'private/context/preprints-tree.json'
        z = json.loads(p.read_text())
        z['truncated'] = True
        p.write_text(json.dumps(z))
    elif name == 'history-edit':
        z = json.loads((pk / 'private/history/register.json').read_text())
        append(c / z[0]['local'])
    elif name == 'context-edit':
        append(pk / 'private/context/fresh-analytic-r128-brief.txt')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    r = a.root.resolve()
    before = snapshot(r)
    results = []
    with tempfile.TemporaryDirectory(prefix='controls-', dir=r / 'work') as td:
        for name in CASES:
            c = Path(td) / name
            c.mkdir()
            shutil.copytree(r / 'packet', c / 'packet', symlinks=True)
            shutil.copyfile(r / 'FINAL.json', c / 'FINAL.json')
            shutil.copyfile(r / 'REPORT.md', c / 'REPORT.md')
            v = c / 'packet/public/verify.py'
            fh, rh = a.final_sha256, a.report_sha256
            if name == 'wrong-final':
                fh = '0' * 64
            if name == 'wrong-report':
                rh = '0' * 64
            mutate(name, c)
            args = ['--root', str(c), '--final-sha256', fh, '--report-sha256', rh]
            if name == 'missing-final':
                args = ['--root', str(c), '--report-sha256', rh]
            cmd = [sys.executable, '-B', str(v), *args]
            if name == 'read-only-audit':
                cmd = [sys.executable, '-B', '-c', AUDIT, str(v), *args]
            p = subprocess.run(cmd, capture_output=True, text=True)
            want = name in ACCEPT
            results.append({'case': name, 'expected': 'accept' if want else 'reject', 'exit': p.returncode,
                            'matched': (p.returncode == 0) == want, 'stdout': p.stdout.strip(),
                            'stderr': p.stderr.strip()[-400:]})
            shutil.rmtree(c)
    after = snapshot(r)
    out = {'kind': 'INTEGRITY_CONTROLS_ONLY', 'detached_final': a.final_sha256,
           'detached_report': a.report_sha256, 'cases': results,
           'original_sealed_files_unchanged': before == after,
           'all_expected': all(x['matched'] for x in results) and before == after}
    print(json.dumps(out, indent=2))
    return 0 if out['all_expected'] else 1


if __name__ == '__main__':
    sys.exit(main())
