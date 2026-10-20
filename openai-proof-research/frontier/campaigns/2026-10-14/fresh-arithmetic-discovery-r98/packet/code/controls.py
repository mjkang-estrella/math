#!/usr/bin/env python3
"""Run the unchanged verifier on transient copies inside the round root; never modifies sealed inputs."""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys
from pathlib import Path

sys.dont_write_bytecode = True
SRC = 'private/upstream/preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/build/build/sections/02-symbols.tex'
PRIMARY = 'private/primary/machala-CasPestMat_100-1975-2_6.pdf'
CASES = ['baseline', 'missing-final-anchor', 'wrong-final-anchor', 'wrong-report-anchor', 'changed-payload',
         'changed-source-body', 'changed-primary-body', 'changed-history-copy', 'missing-file', 'extra-file', 'extra-directory', 'symlink',
         'hardlink', 'mode-change', 'changed-manifest', 'changed-FINAL', 'changed-REPORT']


def snapshot(root, exclude=()):
    rows = {}
    for base, ds, fs in os.walk(root, followlinks=False):
        bp = Path(base)
        ds[:] = [d for d in ds if (bp / d).relative_to(root).as_posix() not in exclude]
        for n in ds + fs:
            p = bp / n
            r = p.relative_to(root).as_posix()
            if r in exclude:
                continue
            s = p.lstat()
            rows[r] = (s.st_mode, s.st_nlink, s.st_size,
                       hashlib.sha256(p.read_bytes()).hexdigest() if stat.S_ISREG(s.st_mode) else None)
    return rows


def append(p):
    p.write_bytes(p.read_bytes() + b' ')


def mutate(dest, case):
    pk = dest / 'packet'
    if case == 'changed-payload':
        append(pk / 'public/report.md')
    elif case == 'changed-source-body':
        append(pk / SRC)
    elif case == 'changed-primary-body':
        append(pk / PRIMARY)
    elif case == 'changed-history-copy':
        append(pk / 'private/history/r97-screens.md')
    elif case == 'missing-file':
        (pk / 'public/RIGHTS.md').unlink()
    elif case == 'extra-file':
        (pk / 'public/extra.txt').write_text('x')
    elif case == 'extra-directory':
        (pk / 'public/extra').mkdir()
    elif case == 'symlink':
        p = pk / 'public/RIGHTS.md'
        data = p.read_bytes()
        p.unlink()
        (dest / 'rights-copy').write_bytes(data)
        p.symlink_to(dest / 'rights-copy')
    elif case == 'hardlink':
        os.link(pk / 'public/RIGHTS.md', dest / 'rights-link')
    elif case == 'mode-change':
        p = pk / 'public/RIGHTS.md'
        os.chmod(p, stat.S_IMODE(p.stat().st_mode) ^ 0o100)
    elif case == 'changed-manifest':
        append(pk / 'MANIFEST.json')
    elif case == 'changed-FINAL':
        append(dest / 'FINAL.json')
    elif case == 'changed-REPORT':
        append(dest / 'REPORT.md')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    r = a.root.resolve()
    work = r / 'control-work'
    excl = ('control-work', 'integrity-results.json')
    before = snapshot(r, excl)
    work.mkdir()
    results = []
    try:
        for case in CASES:
            dest = work / case
            dest.mkdir()
            shutil.copytree(r / 'packet', dest / 'packet', symlinks=True)
            shutil.copy2(r / 'FINAL.json', dest / 'FINAL.json')
            shutil.copy2(r / 'REPORT.md', dest / 'REPORT.md')
            mutate(dest, case)
            cmd = [sys.executable, '-B', str(dest / 'packet/code/verify.py'), '--root', str(dest), '--tree', str(a.tree.resolve()),
                   '--report-sha256', '0' * 64 if case == 'wrong-report-anchor' else a.report_sha256]
            if case != 'missing-final-anchor':
                cmd += ['--final-sha256', '0' * 64 if case == 'wrong-final-anchor' else a.final_sha256]
            snap = snapshot(dest)
            run = subprocess.run(cmd, text=True, capture_output=True)
            unchanged = snapshot(dest) == snap
            expected = (run.returncode == 0) if case == 'baseline' else (run.returncode != 0)
            results.append({'case': case, 'exit_code': run.returncode, 'expected_result': expected,
                            'copy_inputs_unchanged': unchanged, 'stdout': run.stdout.strip(), 'stderr': run.stderr.strip()})
            shutil.rmtree(dest)
    finally:
        shutil.rmtree(work)
    after = snapshot(r, excl)
    receipt = {'final_sha256': a.final_sha256, 'report_sha256': a.report_sha256,
               'verifier_sha256': hashlib.sha256((r / 'packet/code/verify.py').read_bytes()).hexdigest(),
               'controls_sha256': hashlib.sha256((r / 'packet/code/controls.py').read_bytes()).hexdigest(),
               'cases': results,
               'all_expected': all(x['expected_result'] and x['copy_inputs_unchanged'] for x in results),
               'author_root_unchanged_during_replay': before == after,
               'limits': 'artifact controls only; no mathematical tests; tampering is rejected under the original detached anchors; no malicious-resealing or syscall-denial suite'}
    (r / 'integrity-results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'cases': len(results), 'all_expected': receipt['all_expected'],
                      'author_root_unchanged': receipt['author_root_unchanged_during_replay']}))
    if not (receipt['all_expected'] and receipt['author_root_unchanged_during_replay']):
        sys.exit(1)


if __name__ == '__main__':
    main()
