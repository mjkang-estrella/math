#!/usr/bin/env python3
"""MIT. Reviewer-side identity controls for the frozen r49 T197H packet.

Works only on a disposable copy placed under a fresh scratch directory
(default parent /var/tmp). The authenticated author packet is read, never
written. Results are identity/integrity facts, not mathematics.
"""
import argparse, hashlib, importlib.util, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

ANCHOR = '819bc0a77c9ae52ca8a1b2193f64fc2f84754c17b6d5e0750c0be0ae351fd8b2'
VERIFIER = '3483b937b1a143659f6ade296c6bebd1dc177c8122e99adfbfd30c43db06f51a'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def snapshot(root):
    out = {}
    for p in sorted(root.rglob('*')):
        st = p.lstat()
        rel = p.relative_to(root).as_posix()
        if p.is_symlink():
            out[rel] = 'symlink'
        elif p.is_dir():
            out[rel] = 'dir'
        else:
            out[rel] = sha(p.read_bytes()) + ':%d' % st.st_nlink
    return out


def canonical_compare(packet, tree_path):
    raw = tree_path.read_bytes()
    assert sha(raw) == TREE_SHA256, 'canonical tree anchor mismatch'
    tree = json.loads(raw)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    blobs = {e['path']: e for e in tree['tree']}
    seen = []
    for p in sorted((packet / 'private' / 'preprints').rglob('*')):
        if not p.is_file():
            continue
        rel = p.relative_to(packet / 'private').as_posix()
        b = p.read_bytes()
        e = blobs.get(rel)
        if e is None or e['type'] != 'blob' or e['sha'] != git_blob(b) or e['size'] != len(b):
            raise ValueError('canonical blob mismatch: ' + rel)
        seen.append(rel)
    return len(seen)


def load_verifier(path):
    spec = importlib.util.spec_from_file_location('r49_verifier_copy', path)
    v = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    return v


def attempt(fn):
    try:
        return True, fn()
    except Exception as e:  # noqa: BLE001 - record reason
        return False, str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--author', type=Path, required=True)
    ap.add_argument('--tree', type=Path, required=True)
    ap.add_argument('--scratch-parent', type=Path, default=Path('/var/tmp'))
    a = ap.parse_args()
    author = a.author.absolute()
    assert sha((author / 'MANIFEST.json').read_bytes()) == ANCHOR
    assert sha((author / 'verify.py').read_bytes()) == VERIFIER
    before = snapshot(author)
    scratch = Path(tempfile.mkdtemp(prefix='t197h-proof-r1-', dir=a.scratch_parent))
    results = []

    def record(case, expected, ok, reason):
        actual = 'accept' if ok else 'reject'
        assert actual == expected, (case, expected, reason)
        results.append({'case': case, 'expected': expected, 'actual': actual,
                        'detail': reason if isinstance(reason, str) else 'PASS'})

    def fresh(name):
        d = scratch / name
        shutil.copytree(author, d, symlinks=True)
        return d

    try:
        base = fresh('base')
        v = load_verifier(base / 'verify.py')
        ok, r = attempt(lambda: v.check(base, ANCHOR)); record('positive_copy', 'accept', ok, r)
        ok, r = attempt(lambda: v.check(base, '0' * 64)); record('wrong_anchor', 'reject', ok, r)
        n = canonical_compare(base, a.tree)
        results.append({'case': 'independent_canonical_blobs', 'expected': 'match', 'actual': 'match', 'detail': n})

        d = fresh('payload_byte')
        f = d / 'candidate.md'; f.write_bytes(f.read_bytes().replace(b'32/', b'31/', 1))
        ok, r = attempt(lambda: v.check(d, ANCHOR)); record('candidate_one_byte', 'reject', ok, r)

        # Ancestor symlink: documented limit of the author verifier (expected accept).
        d = fresh('ancestor_target')
        link = scratch / 'ancestor-link'; link.symlink_to(scratch, target_is_directory=True)
        ok, r = attempt(lambda: v.check(link / 'ancestor_target', ANCHOR))
        record('ancestor_symlink_author_verifier_limit', 'accept', ok, r)

        # Counterfeit source fully resealed: author verifier trusts copied selection
        # and accepts under the counterfeit's own anchor; only the external anchor
        # and the independent canonical-tree comparison reject it.
        d = fresh('counterfeit_source')
        src = 'preprints/A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026/build/sections/planar.tex'
        body = d / 'private' / src
        nb = body.read_bytes().replace(b'12N', b'99N', 1); body.write_bytes(nb)
        rec = json.loads((d / 'source197-receipts.json').read_text())
        for e in rec['files']:
            if e['path'] == src:
                e['bytes'] = len(nb); e['sha256'] = sha(nb); e['git_blob_sha1'] = git_blob(nb)
        (d / 'source197-receipts.json').write_text(json.dumps(rec, indent=2) + '\n')
        sel = json.loads((d / 'source-tree-selection.json').read_text())
        for e in sel['entries']:
            if e['path'] == src:
                e['sha'] = git_blob(nb)
                if 'size' in e:
                    e['size'] = len(nb)
        (d / 'source-tree-selection.json').write_text(json.dumps(sel, indent=2) + '\n')
        m = json.loads((d / 'MANIFEST.json').read_text())
        for e in m['files']:
            p = d / e['path']
            b = p.read_bytes(); e['bytes'] = len(b); e['sha256'] = sha(b)
        (d / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')
        fake = sha((d / 'MANIFEST.json').read_bytes())
        ok, r = attempt(lambda: v.check(d, ANCHOR)); record('counterfeit_source_external_anchor', 'reject', ok, r)
        ok, r = attempt(lambda: v.check(d, fake)); record('counterfeit_source_self_anchor_author_limit', 'accept', ok, r)
        ok, r = attempt(lambda: canonical_compare(d, a.tree)); record('counterfeit_source_canonical_tree', 'reject', ok, r)

        # Supplied 13 author controls, replayed on a disposable copy.
        d = fresh('author_controls')
        out = subprocess.run([sys.executable, '-B', str(d / 'checks' / 'integrity_controls.py'),
                              '--root', str(d), '--scratch', str(d / 'checks' / 'scratch-r1')],
                             capture_output=True, text=True, check=True)
        ctl = json.loads(out.stdout)
        assert ctl['status'] == 'PASS' and len(ctl['controls']) == 13
        results.append({'case': 'author_supplied_controls', 'expected': 'PASS', 'actual': ctl['status'],
                        'detail': [c['case'] for c in ctl['controls']]})

        out = subprocess.run([sys.executable, '-B', str(d / 'checks' / 'finite_checks.py')],
                             capture_output=True, text=True, check=True)
        same = json.loads(out.stdout) == json.loads((author / 'checks' / 'finite-results.json').read_text())
        assert same
        results.append({'case': 'author_finite_diagnostic_replay', 'expected': 'equal', 'actual': 'equal',
                        'detail': 'finite ribbon/budget diagnostic only; not proof'})
    finally:
        shutil.rmtree(scratch)
    after = snapshot(author)
    assert before == after, 'author packet changed'
    print(json.dumps({'status': 'PASS', 'anchor': ANCHOR, 'verifier_sha256': VERIFIER,
                      'author_nodes_unchanged': len(after), 'controls': results,
                      'scope': 'Identity, inventory and copied-mutation controls only. No mathematical, '
                               'novelty or contribution claim. Ancestor-symlink and self-anchored '
                               'counterfeit-source acceptance are recorded author-verifier limits.'},
                     indent=2))


if __name__ == '__main__':
    main()
