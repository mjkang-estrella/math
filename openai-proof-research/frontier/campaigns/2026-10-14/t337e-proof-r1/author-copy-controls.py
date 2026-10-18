#!/usr/bin/env python3
"""Reason-checked mutation controls for the T337E author verifier. MIT.

Integrity only; proves no mathematics. Runs the AUTHOR verify.py, imported
from a disposable, already authenticated copy of the author packet. Never
point --copy at the canonical packet: every mutation is applied to clones
created under --scratch, which must be an empty directory outside the
research repository.

usage: author-copy-controls.py --copy DIR --scratch EMPTY_DIR --anchor SHA256
"""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path

sys.dont_write_bytecode = True


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--copy', required=True)
    ap.add_argument('--scratch', required=True)
    ap.add_argument('--anchor', required=True)
    a = ap.parse_args()
    copy = Path(a.copy).absolute()
    scratch = Path(a.scratch).absolute()
    if 'openai-proof-research' in str(copy) or 'openai-proof-research' in str(scratch):
        raise SystemExit('refusing: copy and scratch must be outside the research repository')
    if any(scratch.iterdir()):
        raise SystemExit('refusing: scratch must be empty')
    sys.path.insert(0, str(copy))
    from verify import verify  # author verifier, from the disposable copy
    verify(copy, a.anchor)
    manifest = json.loads((copy / 'manifest.json').read_text())

    def clone(name):
        d = scratch / name
        d.mkdir()
        for x in manifest['directories']:
            (d / x).mkdir(parents=True, exist_ok=True)
        for x in list(manifest['files']) + ['manifest.json']:
            (d / x).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(copy / x, d / x)
        return d

    def reseal(d):
        # Recompute the author's manifest format for a deliberately altered clone.
        files = {}
        dirs = []
        for dp, dn, fn in os.walk(d):
            dn.sort()
            for x in dn:
                dirs.append((Path(dp) / x).relative_to(d).as_posix())
            for x in sorted(fn):
                rel = (Path(dp) / x).relative_to(d).as_posix()
                if rel != 'manifest.json':
                    files[rel] = sha(Path(dp) / x)
        (d / 'manifest.json').write_text(json.dumps({'directories': sorted(dirs), 'files': files}, indent=2, sort_keys=True))
        return sha(d / 'manifest.json')

    # name -> (expected exception type, required reason substring)
    expect = {
        'wrong-anchor': ('ValueError', 'external anchor mismatch'),
        'changed-file': ('ValueError', 'exact directory/file inventory mismatch'),
        'missing-file': ('ValueError', 'exact directory/file inventory mismatch'),
        'extra-file': ('ValueError', 'exact directory/file inventory mismatch'),
        'extra-empty-directory': ('ValueError', 'exact directory/file inventory mismatch'),
        'payload-symlink': ('ValueError', 'link/nonregular: diagnostic.py'),
        'directory-symlink': ('ValueError', 'link/nonregular: private/source337'),
        'root-symlink': ('ValueError', 'root/ancestor link or non-directory'),
        'ancestor-symlink': ('ValueError', 'root/ancestor link or non-directory'),
        'hardlinked-payload': ('ValueError', 'hardlink: diagnostic.py'),
        'fifo-payload': ('ValueError', 'link/nonregular: diagnostic.py'),
        'hardlinked-manifest': ('ValueError', 'manifest link/nonregular'),
        'changed-manifest': ('ValueError', 'external anchor mismatch'),
        # Reviewer additions: a source body altered and the manifest resealed under a NEW anchor.
        # The inventory then matches, so rejection must come from the pinned-blob check.
        'resealed-altered-source-blob': ('AssertionError', ''),
        'resealed-altered-canonical-tree-entry': ('KeyError', ''),
    }
    results = {}
    d = clone('positive')
    verify(d, a.anchor)
    results['positive'] = {'control': 'PASS', 'outcome': 'accepted'}
    for name, (etype, reason) in expect.items():
        d = clone(name)
        anchor = a.anchor
        p = d / 'diagnostic.py'
        if name == 'wrong-anchor':
            anchor = '0' * 64
        elif name == 'changed-file':
            p.write_bytes(p.read_bytes() + b'\n# mutation\n')
        elif name == 'missing-file':
            p.unlink()
        elif name == 'extra-file':
            (d / 'extra').write_text('mutation')
        elif name == 'extra-empty-directory':
            (d / 'extra-empty').mkdir()
        elif name == 'payload-symlink':
            p.unlink(); p.symlink_to(copy / 'diagnostic.py')
        elif name == 'directory-symlink':
            shutil.rmtree(d / 'private/source337')
            (d / 'private/source337').symlink_to(copy / 'private/source337', target_is_directory=True)
        elif name == 'root-symlink':
            link = scratch / 'root-link'; link.symlink_to(d, target_is_directory=True); d = link
        elif name == 'ancestor-symlink':
            link = scratch / 'ancestor-link'; link.symlink_to(d.parent, target_is_directory=True); d = link / d.name
        elif name == 'hardlinked-payload':
            os.link(p, scratch / 'payload-hardlink')
        elif name == 'fifo-payload':
            p.unlink(); os.mkfifo(p)
        elif name == 'hardlinked-manifest':
            os.link(d / 'manifest.json', scratch / 'manifest-hardlink')
        elif name == 'changed-manifest':
            (d / 'manifest.json').write_text('{}\n')
        elif name == 'resealed-altered-source-blob':
            q = d / 'private/source337/build/sections/03-radial.tex'
            q.write_bytes(q.read_bytes().replace(b'\\leq n\\int_Y rg', b'\\leq 2n\\int_Y rg', 1))
            anchor = reseal(d)
        elif name == 'resealed-altered-canonical-tree-entry':
            # Rename the bound source path in the copied tree; a resealed inventory
            # still matches, so the binding lookup must fail.
            t = d / 'private/context/sources/preprints-tree.json'
            t.write_text(t.read_text().replace('build/sections/03-radial.tex', 'build/sections/03-radial-x.tex'))
            anchor = reseal(d)
        try:
            verify(d, anchor)
        except Exception as e:
            got = type(e).__name__
            ok = got == etype and reason in str(e)
            results[name] = {'control': 'PASS' if ok else 'FAILED', 'exception': got, 'reason': str(e)[:120],
                             'expected_exception': etype, 'expected_reason_substring': reason}
        else:
            results[name] = {'control': 'FAILED', 'outcome': 'accepted mutation'}

    # Optimization mode strips Python assert statements. Document whether the
    # resealed altered-blob mutation is then accepted.
    d = scratch / 'resealed-altered-source-blob'
    anchor = sha(d / 'manifest.json')
    run = subprocess.run([sys.executable, '-O', '-B', str(copy / 'verify.py'), str(d), anchor],
                         capture_output=True, text=True, timeout=120)
    results['limitation-python-O-resealed-altered-blob'] = {
        'returncode': run.returncode, 'output': (run.stdout + run.stderr).strip()[-120:],
        'note': 'returncode 0 means the author verifier accepts an altered pinned source under python -O; '
                'run it without -O and with the externally supplied anchor'}
    shutil.rmtree(scratch)
    scratch.mkdir()
    status = 'PASS_ALL_REASON_CHECKED' if all(v.get('control') == 'PASS' for k, v in results.items()
                                               if not k.startswith('limitation')) else 'FAILED'
    print(json.dumps({'integrity_only': True, 'status': status, 'author_anchor': a.anchor,
                      'controls': results}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
