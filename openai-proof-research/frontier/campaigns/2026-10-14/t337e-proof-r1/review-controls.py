#!/usr/bin/env python3
"""Copied adversarial controls with reason checks for the T337E proof-review r1 seal. MIT.

Never touches the original packet. --scratch must be an existing, empty,
non-symlink directory outside the packet. Each case recopies the packet into
the scratch directory, mutates the copy, runs a verifier and checks both the
exit status and the exact failure reason. The scratch directory is emptied at
the end.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


# case -> expected reason substring (None: must pass)
CASES = {
    'positive': None,
    'positive_python_O': None,
    'wrong_manifest_anchor': 'manifest external anchor mismatch',
    'wrong_verifier_anchor': 'executing verifier external anchor mismatch',
    'malformed_anchor': 'anchor is not a lowercase SHA256 hex digest',
    'edit_review': 'file size/hash mismatch',
    'edit_review_python_O': 'file size/hash mismatch',
    'edit_private_pdf': 'file size/hash mismatch',
    'delete_review': 'exact file inventory mismatch',
    'delete_private_text': 'exact file inventory mismatch',
    'extra_file': 'exact file inventory mismatch',
    'extra_private_file': 'exact file inventory mismatch',
    'extra_empty_dir': 'exact directory inventory mismatch',
    'nested_manifest': 'nested manifest: private/manifest.json',
    'root_symlink': 'symlink ancestry',
    'ancestor_symlink': 'symlink ancestry',
    'parent_traversal': 'parent traversal in path',
    'payload_symlink': 'symlink: link',
    'hardlink': 'hardlink: ',
    'fifo': 'nonregular: fifo',
    'edit_manifest': 'manifest external anchor mismatch',
    'edit_verifier': 'executing verifier external anchor mismatch',
    'swap_packet_verifier': 'packet verifier external anchor mismatch',
    'self_reseal_review': 'manifest external anchor mismatch',
    'reseal_with_new_seal_py': 'manifest external anchor mismatch',
}


def empty(scratch):
    for child in list(scratch.iterdir()):
        if child.is_symlink() or not child.is_dir():
            child.unlink()
        else:
            shutil.rmtree(child)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', required=True)
    ap.add_argument('--scratch', required=True)
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    src = Path(a.packet).resolve()
    raw_scratch = Path(a.scratch)
    if raw_scratch.is_symlink() or not raw_scratch.is_dir():
        sys.exit('scratch must be an existing non-symlink directory')
    scratch = raw_scratch.resolve()
    if scratch == src or src in scratch.parents or scratch in src.parents:
        sys.exit('scratch must lie outside the packet')
    if any(scratch.iterdir()):
        sys.exit('scratch must be empty')
    results = {}
    for name, expected in CASES.items():
        empty(scratch)
        c = scratch / 'copy'
        shutil.copytree(src, c, symlinks=True)
        mh, vh = a.expected_manifest, a.expected_verifier
        script = c / 'review-verify.py'
        root = str(c)
        flags = ['-B']
        if name.endswith('python_O'):
            flags = ['-B', '-O']
        if name == 'wrong_manifest_anchor':
            mh = '0' * 64
        if name == 'wrong_verifier_anchor':
            vh = '0' * 64
        if name == 'malformed_anchor':
            mh = a.expected_manifest.upper()
        if name in ('edit_review', 'edit_review_python_O'):
            with (c / 'review.md').open('a') as f:
                f.write('\nmutation\n')
        if name == 'edit_private_pdf':
            with (c / 'private' / 'lytchak-wayback.pdf').open('ab') as f:
                f.write(b'\0')
        if name == 'delete_review':
            (c / 'review.md').unlink()
        if name == 'delete_private_text':
            (c / 'private' / 'lytchak-wayback.txt').unlink()
        if name == 'extra_file':
            (c / 'extra.txt').write_text('x')
        if name == 'extra_private_file':
            (c / 'private' / 'extra.txt').write_text('x')
        if name == 'extra_empty_dir':
            (c / 'emptydir').mkdir()
        if name == 'nested_manifest':
            shutil.copy(c / 'manifest.json', c / 'private' / 'manifest.json')
        if name == 'root_symlink':
            (scratch / 'link').symlink_to(c, target_is_directory=True)
            root = str(scratch / 'link')
        if name == 'ancestor_symlink':
            (scratch / 'alias').symlink_to(scratch, target_is_directory=True)
            root = str(scratch / 'alias' / 'copy')
        if name == 'parent_traversal':
            root = str(c / 'private') + os.sep + '..'
        if name == 'payload_symlink':
            (c / 'link').symlink_to('review.md')
        if name == 'hardlink':
            os.link(c / 'review.md', c / 'hardlink.md')
        if name == 'fifo':
            os.mkfifo(c / 'fifo')
        if name == 'edit_manifest':
            with (c / 'manifest.json').open('a') as f:
                f.write(' ')
        if name == 'edit_verifier':
            with script.open('a') as f:
                f.write('\n# mutation\n')
        if name == 'swap_packet_verifier':
            runner = scratch / 'runner'
            runner.mkdir()
            shutil.copy(script, runner / 'review-verify.py')
            with script.open('a') as f:
                f.write('\n# mutation\n')
            script = runner / 'review-verify.py'
        if name == 'self_reseal_review':
            p = c / 'review.md'
            p.write_text(p.read_text().replace('NOT_PASS_R1_REQUIRED_REPAIR', 'PASS_FULL_T337E'))
            m = json.loads((c / 'manifest.json').read_text())
            m['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
            (c / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
        if name == 'reseal_with_new_seal_py':
            p = c / 'reading-limits.md'
            with p.open('a') as f:
                f.write('\nmutation\n')
            subprocess.run([sys.executable, '-B', str(c / 'seal.py'), str(c)], check=True, timeout=30)
        cmd = [sys.executable, *flags, str(script), '--root', root,
               '--expected-manifest', mh, '--expected-verifier', vh]
        run = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        out = (run.stdout + run.stderr).strip()
        last = out.split('\n')[-1] if out else ''
        if expected is None:
            ok = run.returncode == 0 and json.loads(last).get('status') == 'PASS'
        else:
            ok = run.returncode == 1 and last.startswith('FAIL: ') and expected in last
        results[name] = {'control': 'PASS' if ok else 'FAILED', 'returncode': run.returncode,
                         'expected_reason': expected,
                         'message': last.replace(str(scratch), '<scratch>')[:160]}
    empty(scratch)
    status = ('PASS_ALL_REVIEW_CONTROLS_REASON_CHECKED'
              if all(r['control'] == 'PASS' for r in results.values()) else 'CONTROL_FAILURE')
    print(json.dumps({'status': status, 'cases': results}, sort_keys=True, indent=2))
    sys.exit(0 if status.startswith('PASS') else 1)


if __name__ == '__main__':
    main()
