#!/usr/bin/env python3
"""Independent identity checks for the frozen T221R author packet. MIT.

Reads the frozen packet only. Every mutation happens in a disposable copy
under this review directory's .scratch/, which is removed before exit.
Hashes and these controls certify byte identity, never a theorem or a
contribution verdict.

Modes:
  --author  : anchors, canonical Git-blob comparison, author verifier replay,
              and copied mutation controls against the author verifier.
  --own     : copied mutation controls against this packet's verify.py
              (requires the external anchors of the sealed packet).
"""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys
from pathlib import Path

PKT_REL = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r44'
AUTHOR_MANIFEST = 'c288940c8c88f67a7374d998a7c49d822f64000abb981517303f1bf4af9739c6'
FAM221 = 'preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/'
FAMSY = 'preprints/The-Solomon-Yau-least-volume-theorem-September-23-2026/'
ANCHORS = {
    PKT_REL + '/manifest.json': AUTHOR_MANIFEST,
    PKT_REL + '/verify.py': '22bc163b277aa160698b01a7d3a4104e3025c7a17cdd51274ddbbb59f2c38b82',
    PKT_REL + '/controls.py': '93425bee00ffa83114837541a0961c7adc7c6dd7c24781b6f17c226539d51583',
    PKT_REL + '/proof.md': 'c2d6631489bc3e2c31dfd2eb986a1987ff477b55c3a837556e3a0923a67fefa0',
    PKT_REL + '/original-scope.txt': '26312b8fd6fb6a4bacb27085f0b46b760cc8f884754bed03e937c1b40328693c',
    PKT_REL + '/reading-and-comparison.md': '11d63dd5cfbf1a6b63a0fdbcadc7dda31a4f0c933c0ea3462d4843678ddebc1d',
    'sources/preprints-tree.json': 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b',
}


def sha256(b): return hashlib.sha256(b).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def run(cmd, timeout=300):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, (p.stdout + p.stderr).strip()


def canonical_compare(pkt, tree_file):
    tree = json.loads(Path(tree_file).read_text())
    if tree.get('truncated') is not False:
        raise SystemExit('tree not complete')
    out = {}
    for fam in (FAM221, FAMSY):
        canon = {x['path']: x['sha'] for x in tree['tree']
                 if x['type'] == 'blob' and x['path'].startswith(fam)}
        local_root = pkt / 'private' / fam
        local = set()
        for dp, dn, fn in os.walk(local_root):
            for f in fn:
                local.add((Path(dp) / f).relative_to(pkt / 'private').as_posix())
        rows, mism = 0, []
        for path, sha in sorted(canon.items()):
            p = pkt / 'private' / path
            if not p.exists():
                if not path.endswith('.pdf'):
                    mism.append('missing:' + path)
                continue
            rows += 1
            if gitblob(p.read_bytes()) != sha:
                mism.append('blob:' + path)
        extra = sorted(local - set(canon))
        out[fam] = {'canonical_blobs': len(canon), 'local_matched_checked': rows,
                    'canonical_pdf_not_copied': sorted(k.rsplit('/', 1)[1] for k in canon
                                                       if k.endswith('.pdf') and k not in local),
                    'mismatches': mism, 'extra_local': extra,
                    'match': not mism and not extra}
    return out


def flip(h): return h[:-1] + ('0' if h[-1] != '0' else '1')


def reseal(c):
    """Rewrite a copy's author manifest to its mutated bytes; returns new anchor."""
    m = json.loads((c / 'manifest.json').read_text())
    files, dirs = {}, []
    for dp, dn, fn in os.walk(c):
        for d in dn: dirs.append((Path(dp) / d).relative_to(c).as_posix())
        for f in fn:
            rel = (Path(dp) / f).relative_to(c).as_posix()
            if rel == 'manifest.json': continue
            b = (Path(dp) / f).read_bytes()
            files[rel] = {'sha256': sha256(b), 'bytes': len(b)}
    m['files'] = files; m['directories'] = sorted(dirs)
    data = (json.dumps(m, indent=2, sort_keys=True) + '\n').encode()
    (c / 'manifest.json').write_bytes(data)
    return sha256(data)


def author_controls(pkt, tree_file, scratch):
    res = {}
    def av(root, anchor):
        return run([sys.executable, '-B', str(root / 'verify.py'), '--root', str(root), '--anchor', anchor])
    src = FAM221 + 'build/sections/decorrelation.tex'
    cases = {
        'copied_positive': (True, None),
        'wrong_anchor': (False, None),
        'edit_proof': (False, lambda c: (c / 'proof.md').write_bytes((c / 'proof.md').read_bytes() + b' ')),
        'edit_scope': (False, lambda c: (c / 'original-scope.txt').write_bytes(
            (c / 'original-scope.txt').read_bytes().replace(b'd>=3', b'd>=2', 1))),
        'edit_source221_blob': (False, lambda c: (c / 'private' / src).write_bytes(
            (c / 'private' / src).read_bytes().replace(b'uses only these', b'uses mostly these', 1))),
        'edit_source221_blob_resealed': (False, 'reseal_src'),
        'edit_primary_pdf': (False, lambda c: (c / 'private/primary/cop2019.pdf').write_bytes(
            (c / 'private/primary/cop2019.pdf').read_bytes() + b'\n')),
        'edit_primary_pdf_resealed': (False, 'reseal_pdf'),
        'edit_primary_txt_resealed': (False, 'reseal_txt'),
        'delete_receipt': (False, lambda c: (c / 'source-221-receipts.json').unlink()),
        'extra_file': (False, lambda c: (c / 'note.txt').write_text('x')),
        'extra_dir': (False, lambda c: (c / 'private' / 'empty').mkdir()),
        'nested_manifest': (False, lambda c: (c / 'private' / 'manifest.json').write_text('{}')),
        'payload_symlink': (False, lambda c: (c / 'link').symlink_to('proof.md')),
        'hardlink': (False, lambda c: os.link(c / 'proof.md', c / 'private' / 'proof-hl.md')),
        'fifo': (False, lambda c: os.mkfifo(c / 'fifo')),
    }
    for name, (expect_pass, mut) in cases.items():
        c = scratch / ('a-' + name)
        shutil.copytree(pkt, c, symlinks=True)
        anchor = AUTHOR_MANIFEST if name != 'wrong_anchor' else flip(AUTHOR_MANIFEST)
        before = None
        if callable(mut):
            mut(c)
        elif mut == 'reseal_src':
            p = c / 'private' / src; old = p.read_bytes()
            p.write_bytes(old.replace(b'uses only these', b'uses mostly these', 1))
            if p.read_bytes() == old: raise SystemExit('no-op mutation')
            anchor = reseal(c)
        elif mut == 'reseal_pdf':
            p = c / 'private/primary/cop2019.pdf'; p.write_bytes(p.read_bytes() + b'\n'); anchor = reseal(c)
        elif mut == 'reseal_txt':
            p = c / 'private/primary/cop2019.txt'; p.write_bytes(p.read_bytes().replace(b'smooth cliff', b'rough cliff', 1))
            anchor = reseal(c)
        rc, out = av(c, anchor)
        row = {'expect_pass': expect_pass, 'rc': rc, 'ok': (rc == 0) == expect_pass}
        try: row['reason'] = json.loads(out.splitlines()[-1]).get('reason', json.loads(out.splitlines()[-1]).get('status'))[:120]
        except Exception: row['reason'] = out[-120:]
        if name.startswith('edit_source221'):
            cc = canonical_compare(c, tree_file)
            row['independent_canonical_detects'] = not cc[FAM221]['match']
            row['ok'] = row['ok'] and row['independent_canonical_detects']
        res[name] = row
        shutil.rmtree(c)
    # Root and ancestor symlinks: author verifier rejects the former; the latter is a documented gap.
    c = scratch / 'a-link-target'; shutil.copytree(pkt, c, symlinks=True)
    rl = scratch / 'a-root-link'; rl.symlink_to(c, target_is_directory=True)
    rc, out = av(rl, AUTHOR_MANIFEST)
    res['root_symlink'] = {'expect_pass': False, 'rc': rc, 'ok': rc != 0}
    anc = scratch / 'a-anc-link'; anc.symlink_to(scratch, target_is_directory=True)
    rc, out = av(anc / 'a-link-target', AUTHOR_MANIFEST)
    res['ancestor_symlink_observed'] = {'rc': rc, 'author_verifier_accepts': rc == 0,
                                       'note': 'author verifier has no ancestor-symlink check; recorded as optional objection O1'}
    rl.unlink(); anc.unlink(); shutil.rmtree(c)
    return res


def author_mode(repo, scratch):
    pkt = repo / PKT_REL
    anchors = {}
    for rel, want in ANCHORS.items():
        h = sha256((repo / rel).read_bytes())
        anchors[rel] = {'sha256': h, 'match': h == want}
    tree_file = repo / 'sources/preprints-tree.json'
    canon = canonical_compare(pkt, tree_file)
    rc_pos, out_pos = run([sys.executable, '-B', str(pkt / 'verify.py'), '--anchor', AUTHOR_MANIFEST])
    rc_neg, _ = run([sys.executable, '-B', str(pkt / 'verify.py'), '--anchor', flip(AUTHOR_MANIFEST)])
    replay = {'positive_rc': rc_pos, 'positive': json.loads(out_pos) if rc_pos == 0 else out_pos,
              'wrong_anchor_rc': rc_neg}
    ctrl = author_controls(pkt, tree_file, scratch)
    after = sha256((pkt / 'manifest.json').read_bytes()) == AUTHOR_MANIFEST and \
        run([sys.executable, '-B', str(pkt / 'verify.py'), '--anchor', AUTHOR_MANIFEST])[0] == 0
    ok = (all(a['match'] for a in anchors.values()) and all(v['match'] for v in canon.values())
          and rc_pos == 0 and rc_neg != 0 and all(v.get('ok', True) for v in ctrl.values()) and after)
    return {'status': 'PASS_IDENTITY_ONLY' if ok else 'FAIL', 'anchors': anchors,
            'canonical_comparison': canon, 'author_verifier_replay': replay,
            'author_copied_controls': ctrl, 'frozen_packet_unchanged_after': after,
            'scope': 'byte identity only; no theorem, proof, or contribution conclusion'}


def own_mode(me, mh, vh, repo, scratch):
    res = {}
    def ov(root, m, v, extra=()):
        return run([sys.executable, '-B', str(root / 'verify.py'), '--expected-manifest', m,
                    '--expected-verifier', v, '--repo', str(repo), *extra])[0]
    def cp(name):
        c = scratch / ('o-' + name); c.mkdir()
        for f in os.listdir(me):
            if f in ('.scratch',): continue
            shutil.copy2(me / f, c / f)
        return c
    cases = {
        'positive': (True, None), 'wrong_manifest': (False, 'm'), 'wrong_verifier': (False, 'v'),
        'edit_report': (False, lambda c: (c / 'report.md').write_bytes((c / 'report.md').read_bytes() + b' ')),
        'delete_limits': (False, lambda c: (c / 'reading-limits.md').unlink()),
        'extra_file': (False, lambda c: (c / 'x.txt').write_text('x')),
        'extra_dir': (False, lambda c: (c / 'd').mkdir()),
        'nested_manifest': (False, lambda c: ((c / 'd').mkdir(), (c / 'd' / 'manifest.json').write_text('{}'))),
        'hardlink': (False, lambda c: os.link(c / 'report.md', c / 'r2.md')),
        'fifo': (False, lambda c: os.mkfifo(c / 'f')),
        'payload_symlink': (False, lambda c: (c / 'l').symlink_to('report.md')),
        'self_reseal': (False, 'reseal'),
    }
    for name, (ep, mut) in cases.items():
        c = cp(name); m, v = mh, vh
        if mut == 'm': m = flip(mh)
        elif mut == 'v': v = flip(vh)
        elif mut == 'reseal':
            (c / 'report.md').write_bytes((c / 'report.md').read_bytes() + b' ')
            man = json.loads((c / 'manifest.json').read_text())
            b = (c / 'report.md').read_bytes()
            man['files']['report.md'] = {'bytes': len(b), 'sha256': sha256(b)}
            (c / 'manifest.json').write_text(json.dumps(man, indent=2, sort_keys=True) + '\n')
        elif callable(mut): mut(c)
        rc = ov(c, m, v)
        res[name] = {'expect_pass': ep, 'rc': rc, 'ok': (rc == 0) == ep}
        shutil.rmtree(c)
    c = cp('root-target')
    rl = scratch / 'o-root-link'; rl.symlink_to(c, target_is_directory=True)
    rc = ov(rl, mh, vh); res['root_symlink'] = {'expect_pass': False, 'rc': rc, 'ok': rc != 0}
    anc = scratch / 'o-anc'; anc.symlink_to(scratch, target_is_directory=True)
    rc = ov(anc / 'o-root-target', mh, vh); res['ancestor_symlink'] = {'expect_pass': False, 'rc': rc, 'ok': rc != 0}
    rl.unlink(); anc.unlink(); shutil.rmtree(c)
    ok = all(r['ok'] for r in res.values())
    return {'status': 'PASS_IDENTITY_ONLY' if ok else 'FAIL', 'own_copied_controls': res}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--author', action='store_true')
    g.add_argument('--own', action='store_true')
    ap.add_argument('--expected-manifest'); ap.add_argument('--expected-verifier')
    a = ap.parse_args()
    repo = Path(os.path.abspath(a.repo)); me = Path(os.path.abspath(__file__)).parent
    scratch = me / '.scratch'
    if scratch.exists(): raise SystemExit('stale scratch present')
    scratch.mkdir()
    try:
        r = author_mode(repo, scratch) if a.author else own_mode(me, a.expected_manifest, a.expected_verifier, repo, scratch)
    finally:
        shutil.rmtree(scratch)
    print(json.dumps(r, indent=2, sort_keys=True))
    sys.exit(0 if r['status'].startswith('PASS') else 1)


if __name__ == '__main__':
    main()
