#!/usr/bin/env python3
"""Independent identity checks for the frozen T047N author packet. MIT.

Reads the frozen packet only. Every mutation happens in a disposable copy under
/var/tmp. Hashes and these controls certify byte identity, never a theorem.
"""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path

PKT_REL = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29'
SRC047 = 'preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/'
COMP = ('preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/',
        'preprints/An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026/')


def sha256(b): return hashlib.sha256(b).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def local_for(tree_path):
    if tree_path.startswith(SRC047):
        return 'private/source047/' + tree_path.rsplit('/', 1)[1]
    if tree_path.startswith(COMP):
        return 'private/companions/' + tree_path
    return None


def independent_blobs(pkt, tree_file):
    tree = json.loads(Path(tree_file).read_text())
    if tree.get('truncated') is not False:
        raise SystemExit('tree not complete')
    rows = []
    for x in tree['tree']:
        if x['type'] != 'blob' or x['path'].endswith('.pdf'):
            continue
        loc = local_for(x['path'])
        if loc is None:
            continue
        b = (pkt / loc).read_bytes()
        rows.append({'path': x['path'], 'local': loc, 'tree_sha1': x['sha'],
                     'local_git_sha1': gitblob(b), 'match': gitblob(b) == x['sha']})
    return rows


def run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    return p.returncode, (p.stdout + p.stderr).strip()


def controls(pkt, tree_file, mh, vh):
    out = {}
    td = Path(tempfile.mkdtemp(prefix='t047n-contrib-r1-', dir='/var/tmp'))
    try:
        cases = ['positive_full_tree', 'positive_no_tree', 'public_only_with_private_present',
                 'public_only_private_removed', 'public_only_with_tree', 'wrong_manifest',
                 'wrong_verifier', 'edit_candidate', 'edit_scope', 'delete_credit',
                 'extra_file', 'extra_dir', 'nested_manifest', 'hardlink', 'fifo',
                 'payload_symlink', 'root_symlink', 'ancestor_symlink', 'edit_source047_with_tree',
                 'edit_companion_with_tree', 'truncated_tree', 'self_reseal', 'edit_verifier_copy']
        for name in cases:
            c = td / name
            shutil.copytree(pkt, c, symlinks=True)
            inv = c; m = mh; v = vh; extra = ['--source-tree', str(tree_file)]
            expect_pass = name in ('positive_full_tree', 'positive_no_tree', 'public_only_private_removed')
            if name == 'positive_no_tree': extra = []
            if name == 'public_only_with_private_present': extra = ['--public-only']
            if name == 'public_only_private_removed': shutil.rmtree(c / 'private'); extra = ['--public-only']
            if name == 'public_only_with_tree': shutil.rmtree(c / 'private'); extra = ['--public-only', '--source-tree', str(tree_file)]
            if name == 'wrong_manifest': m = m[:-1] + ('0' if m[-1] != '0' else '1')
            if name == 'wrong_verifier': v = v[:-1] + ('0' if v[-1] != '0' else '1')
            if name == 'edit_candidate':
                p = c / 'candidate-047.md'; old = p.read_bytes(); new = old.replace(b'ceil(r/n)', b'floor(r/n)', 1)
                if new == old: raise SystemExit('no-op mutation')
                p.write_bytes(new)
            if name == 'edit_scope': (c / 'scope-047.md').write_bytes((c / 'scope-047.md').read_bytes() + b' ')
            if name == 'delete_credit': (c / 'source-and-credit.md').unlink()
            if name == 'extra_file': (c / 'note.txt').write_text('x')
            if name == 'extra_dir': (c / 'private' / 'empty').mkdir()
            if name == 'nested_manifest': (c / 'private' / 'manifest.json').write_text('{}')
            if name == 'hardlink': os.link(c / 'scope-047.md', c / 'private' / 'scope-hl.md')
            if name == 'fifo': os.mkfifo(c / 'pipe')
            if name == 'payload_symlink':
                (c / 'reading-limits.md').unlink(); (c / 'reading-limits.md').symlink_to(c / 'checkpoint.md')
            if name == 'root_symlink':
                inv = td / 'rootlink'; inv.symlink_to(c, target_is_directory=True)
            if name == 'ancestor_symlink':
                h = td / 'h'; h.mkdir(); shutil.move(str(c), str(h / 'pkt'))
                (td / 'hl').symlink_to(h, target_is_directory=True); inv = td / 'hl' / 'pkt'
            if name == 'edit_source047_with_tree':
                p = c / 'private/source047/06-rigidity.tex'; old = p.read_bytes()
                new = old.replace(b'Mason', b'Masom', 1)
                if new == old: raise SystemExit('no-op mutation')
                p.write_bytes(new)
            if name == 'edit_companion_with_tree':
                p = next((c / 'private/companions').rglob('paper.tex')); p.write_bytes(p.read_bytes() + b'%')
            if name == 'truncated_tree':
                t = json.loads(Path(tree_file).read_text()); t['truncated'] = True
                tt = td / 'trunc.json'; tt.write_text(json.dumps(t)); extra = ['--source-tree', str(tt)]
            if name == 'self_reseal':
                p = c / 'candidate-047.md'; p.write_bytes(p.read_bytes() + b'\nmut\n')
                mm = json.loads((c / 'manifest.json').read_text())
                mm['files']['candidate-047.md'] = {'bytes': p.stat().st_size, 'sha256': sha256(p.read_bytes())}
                (c / 'manifest.json').write_text(json.dumps(mm, indent=2, sort_keys=True) + '\n')
            if name == 'edit_verifier_copy':
                (c / 'verify.py').write_bytes((c / 'verify.py').read_bytes() + b'\n# m\n')
            rc, msg = run([sys.executable, '-I', str(inv / 'verify.py'), '--expected-manifest', m,
                           '--expected-verifier', v, *extra])
            ok = (rc == 0) if expect_pass else (rc != 0)
            out[name] = {'expected': 'PASS' if expect_pass else 'REJECT', 'rc': rc,
                         'message': msg.splitlines()[-1] if msg else '', 'control_ok': ok}
    finally:
        shutil.rmtree(td)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True)
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    repo = Path(os.path.abspath(a.repo)); pkt = repo / PKT_REL
    tree = repo / 'sources/preprints-tree.json'
    for q in [pkt, *pkt.parents]:
        if stat.S_ISLNK(q.lstat().st_mode):
            raise SystemExit('symlink ancestry ' + str(q))
    anchors = {k: sha256((pkt / k).read_bytes()) for k in ['manifest.json', 'verify.py', 'candidate-047.md', 'scope-047.md']}
    anchors['preprints-tree.json'] = sha256(tree.read_bytes())
    clar = repo / 'frontier/campaigns/2026-10-14/t047n-author-primary-clarification-r1/clarification.md'
    anchors['clarification.md'] = sha256(clar.read_bytes())
    blobs = independent_blobs(pkt, tree)
    res = {'anchors': anchors, 'independent_blob_count': len(blobs),
           'independent_blobs_all_match': all(r['match'] for r in blobs), 'blobs': blobs,
           'controls': controls(pkt, tree, a.expected_manifest, a.expected_verifier)}
    res['all_controls_ok'] = all(v['control_ok'] for v in res['controls'].values())
    print(json.dumps(res, indent=2, sort_keys=True))
    sys.exit(0 if res['all_controls_ok'] and res['independent_blobs_all_match'] else 1)


if __name__ == '__main__':
    main()
