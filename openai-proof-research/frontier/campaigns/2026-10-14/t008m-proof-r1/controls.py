#!/usr/bin/env python3
"""Copied mutation controls for the review seal.  Writes only to disposable
/var/tmp copies; the original directory is never modified.  MIT."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


CASES = ['positive', 'wrong_manifest_anchor', 'edit_review', 'delete_review', 'extra_file',
         'extra_empty_dir', 'symlink_inside', 'root_symlink', 'ancestor_symlink', 'hardlink_out',
         'fifo', 'edit_verifier', 'self_reseal']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest-sha256', required=True)
    a = ap.parse_args()
    src = Path(os.path.abspath(__file__)).parent
    if sha(src / 'manifest.json') != a.manifest_sha256:
        raise SystemExit('external anchor mismatch before controls')
    out = []
    for case in CASES:
        with tempfile.TemporaryDirectory(prefix='t008m-review-ctl-', dir='/var/tmp') as tmp:
            tmp = Path(tmp)
            d = tmp / 'real' / 'review'
            shutil.copytree(src, d, symlinks=True)
            inv = d
            anchor = a.manifest_sha256
            if case == 'wrong_manifest_anchor':
                anchor = '0' * 64
            elif case == 'edit_review':
                (d / 'review.md').write_text('**FAIL**\n')
            elif case == 'delete_review':
                (d / 'review.md').unlink()
            elif case == 'extra_file':
                (d / 'extra.txt').write_text('x\n')
            elif case == 'extra_empty_dir':
                (d / 'empty').mkdir()
            elif case == 'symlink_inside':
                (d / 'link').symlink_to(d / 'review.md')
            elif case == 'root_symlink':
                (tmp / 'rootlink').symlink_to(d, target_is_directory=True)
                inv = tmp / 'rootlink'
            elif case == 'ancestor_symlink':
                (tmp / 'anc').symlink_to(tmp / 'real', target_is_directory=True)
                inv = tmp / 'anc' / 'review'
            elif case == 'hardlink_out':
                os.link(d / 'review.md', tmp / 'outside-hardlink')
            elif case == 'fifo':
                os.mkfifo(d / 'pipe')
            elif case == 'edit_verifier':
                p = d / 'verify.py'
                p.write_text(p.read_text().replace("fail('payload mismatch: ' + name)", 'pass'))
            elif case == 'self_reseal':
                p = d / 'review.md'
                p.write_text('**FAIL**\n')
                mp = d / 'manifest.json'
                m = json.loads(mp.read_text())
                m['files']['review.md'] = {'sha256': sha(p), 'bytes': p.stat().st_size}
                mp.write_text(json.dumps(m, indent=1, sort_keys=True) + '\n')
            # A modified verifier can always accept itself, so the caller must
            # authenticate verify.py against the externally anchored manifest
            # before executing it.  This preflight models that caller step.
            pre = None
            mp = inv / 'manifest.json'
            if not mp.is_file() or sha(mp) != anchor:
                pre = 'PREFLIGHT FAIL: manifest does not match external anchor'
            else:
                row = json.loads(mp.read_text()).get('files', {}).get('verify.py', {})
                if sha(inv / 'verify.py') != row.get('sha256'):
                    pre = 'PREFLIGHT FAIL: verify.py differs from anchored manifest row'
            # Run the verifier regardless so its own rejection is also recorded.
            r = subprocess.run([sys.executable, str(inv / 'verify.py'), '--manifest-sha256', anchor],
                               capture_output=True, text=True, timeout=30)
            accepted = pre is None and r.returncode == 0
            expect = case == 'positive'
            ok = accepted == expect
            if case not in ('positive', 'edit_verifier'):
                ok = ok and r.returncode != 0  # verifier itself must reject these
            out.append({'case': case, 'expected_accept': expect, 'preflight': pre or 'ok',
                        'verifier_exit_code': r.returncode, 'passed': ok,
                        'message': (r.stdout + r.stderr).strip()})
            if not ok:
                print(json.dumps(out, indent=1))
                raise SystemExit('control failed: ' + case)
    print(json.dumps({'status': 'PASS_COPIED_CONTROLS_NOT_PROOF', 'cases': out}, indent=1))


if __name__ == '__main__':
    main()
