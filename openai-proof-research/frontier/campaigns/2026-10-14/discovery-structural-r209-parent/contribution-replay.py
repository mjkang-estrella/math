#!/usr/bin/env python3
"""Read-only contribution packet binding; mutate only tiny parent-local controls."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, tempfile

P = Path(__file__).resolve().parent
C = P.parent
PROJECT = C.parents[2]
A = C / 'fresh-structural-discovery-r209'
R = C / 'structural-r209-contribution-r1'
read = lambda p: json.loads(p.read_bytes())
sha = lambda b: hashlib.sha256(b).hexdigest()
anchors = {
    'FINAL': '8a5095126eaeea533cd1f6fd6624c02faa370c828e2274b11867816874c02260',
    'MANIFEST': '0e437f4c0f528feb886e222b6866e627be885107067a1cd26a546e4fea92c0f8',
    'REPORT': '7187f5352d078cdde498d3e17f5b43a63b46c9c6ca1040e3d4369be69720f2d4',
}

def observe(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e = {'type': 'directory' if p.is_dir() else 'file', 'mode': format(stat.S_IMODE(p.stat().st_mode), '04o')}
        if p.is_file():
            b = p.read_bytes()
            e.update(bytes=len(b), sha256=sha(b))
        out['.' if p == root else p.relative_to(root).as_posix()] = e
    return out

def run(verifier, root, aa):
    args = ['python3', '-I', '-B', str(verifier), '--root', str(root)]
    for k in ['FINAL', 'MANIFEST', 'REPORT']:
        args.extend(['--' + k.lower() + '-sha256', aa[k]])
    return subprocess.run(args, capture_output=True, text=True)

before = observe(R)
author_before = observe(A)
assert author_before == read(P / 'observed-root.json')
assert sha((R / 'verify_packet.py').read_bytes()) == '92bd50053235b94eb06ee8d77ef406713c76e4d6f462a2ae6923e1577975e2e1'
v = run(R / 'verify_packet.py', R, anchors)
assert v.returncode == 0, (v.stdout, v.stderr)
av = run(A / 'verify_packet.py', A, read(P / 'replay.json')['anchors'])
assert av.returncode == 0, (av.stdout, av.stderr)
tb = (PROJECT / 'sources/preprints-tree.json').read_bytes()
assert sha(tb) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = {e['path']: e for e in json.loads(tb)['tree']}
canon = {e['path']: e for e in read(A / 'private/authenticated-source.json')}
sources = read(R / 'private/source-authentication.json')
assert len(sources) == 14
for e in sources:
    old = canon[e['path']]
    assert all(e[k] == old[k] for k in ['path', 'bytes', 'sha256', 'git_blob'])
    b = (A / old['local']).read_bytes()
    assert len(b) == e['bytes'] == tree[e['path']]['size'] and sha(b) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == e['git_blob'] == tree[e['path']]['sha']
import base64
for name, copy in [('lean-doc-metadata.json', 'lean-333.md'), ('lean-comparator-metadata.json', 'SurfaceImmersion.lean')]:
    e = read(R / 'private/retrieved' / name)
    b = (A / 'private' / copy).read_bytes()
    assert base64.b64decode(e['content']) == b and len(b) == e['size']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == e['sha']
primaries = read(R / 'private/primary-identities.json')
for e in primaries:
    b = (A / 'private/primary' / (e['name'] + '.pdf')).read_bytes()
    assert len(b) == e['bytes'] and sha(b) == e['sha256']
    assert sha((A / 'private/primary' / (e['name'] + '.txt')).read_bytes()) == e['extracted_text_sha256']
new_access = read(R / 'private/new-access.json')
new_pdfs = [('DAmbraLoi2007', next(e for e in new_access if e['name'] == 'DAmbraLoi2007')), ('Gromov1986', read(R / 'private/retrieved/Gromov1986-access.json'))]
for name, e in new_pdfs:
    b = (R / 'private/retrieved' / (name + '.pdf')).read_bytes()
    assert len(b) == e['bytes'] and sha(b) == e['sha256']
for name in ['AUTHOR-PROOF.md', 'FROZEN-STATEMENT.md']:
    assert (R / 'private/scope' / name).read_bytes() == (A / name).read_bytes()
history = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/proof.md'
author_prefix = A.relative_to(PROJECT).as_posix() + '/'
review_prefix = R.relative_to(PROJECT).as_posix() + '/'
extents = read(R / 'private/reading-extents.json')
page_count = 0
for e in extents:
    name = e['original']
    if name == history:
        lo, hi = e['read_bytes']
        assert (lo, hi) in {(0, 929), (3544, 11553)}
        with (PROJECT / name).open('rb') as f:
            f.seek(lo)
            b = f.read(hi - lo)
        assert sha(b) == e['sha256']
        assert b == (R / f'private/scope/original-r107-{lo}-{hi}.txt').read_bytes()
        continue
    if name.startswith(author_prefix):
        assert name[len(author_prefix):] in author_before
    else:
        assert name.startswith(review_prefix) and name[len(review_prefix):] in before
    b = (PROJECT / name).read_bytes()
    assert sha(b) == e['sha256']
    if 'read_bytes' in e:
        assert e['read_bytes'] == [0, len(b)]
    else:
        pages = b.split(b'\x0c')
        assert e['pdf_pages_read'] == [x['pdf_page'] for x in e['extracted_text_extents']]
        for x in e['extracted_text_extents']:
            page = x['pdf_page'] - 1
            offset = sum(len(z) + 1 for z in pages[:page])
            assert x['text_bytes'] == [offset, offset + len(pages[page])]
            page_count += 1
visual = read(R / 'private/visual-read-extents.json')
visual_count = 0
for key, pages in visual.items():
    if key == 'rendered_but_not_visually_read':
        assert all((R / 'private/renders' / name).is_file() for name in pages)
        continue
    owner, name = key.removesuffix('_pdf_pages').split('_', 1)
    for page in pages:
        if owner == 'author':
            f = A / 'private/primary' / f'{name}-view-{page:02d}.png'
        else:
            assert owner == 'own'
            names = sorted({f'{name}-{page:02d}.png', f'{name}-{page:03d}.png'})
            matches = [R / 'private/renders' / n for n in names if (R / 'private/renders' / n).is_file()]
            assert len(matches) == 1
            f = matches[0]
        assert f.is_file()
        visual_count += 1
assert sha((R / 'private/acceptance.txt').read_bytes()) == 'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'

controls = []
with tempfile.TemporaryDirectory(prefix='contribution-controls-', dir=P) as tmp:
    base = R / 'private/integrity-control'
    ca = {k: sha((base / (k + '.md' if k in ['FINAL', 'REPORT'] else 'MANIFEST.json')).read_bytes()) for k in anchors}
    for case in ['intact', 'wrong-anchor', 'changed-bytes', 'extra-file', 'missing-file', 'file-mode', 'directory-mode']:
        dst = Path(tmp) / case
        shutil.copytree(base, dst)
        aa = dict(ca)
        f = dst / 'payload.txt'
        if case == 'wrong-anchor':
            aa['FINAL'] = '0' * 64
        elif case == 'changed-bytes':
            b = f.read_bytes()
            mode = stat.S_IMODE(f.stat().st_mode)
            f.chmod(0o600)
            f.write_bytes(bytes([b[0] ^ 1]) + b[1:])
            f.chmod(mode)
        elif case == 'extra-file':
            (dst / 'extra.txt').write_text('extra\n')
        elif case == 'missing-file':
            f.unlink()
        elif case == 'file-mode':
            f.chmod(stat.S_IMODE(f.stat().st_mode) ^ 0o100)
        elif case == 'directory-mode':
            dst.chmod(stat.S_IMODE(dst.stat().st_mode) ^ 0o020)
        q = run(R / 'verify_packet.py', dst, aa)
        accepted = q.returncode == 0
        assert accepted == (case == 'intact'), (case, q.stdout, q.stderr)
        controls.append({'case': case, 'accepted': accepted, 'expected': case == 'intact'})
assert observe(R) == before and observe(A) == author_before
out = {
    'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'artifact_only': True, 'anchors': anchors, 'verification': json.loads(v.stdout),
    'author_verification': json.loads(av.stdout), 'review_files': len([e for e in before.values() if e['type'] == 'file']),
    'review_directories': len([e for e in before.values() if e['type'] == 'directory']),
    'author_files_unchanged': 85, 'review_originals_unchanged': True,
    'canonical_blob_bindings': 14, 'formal_bindings': 2, 'retained_primary_pairs': len(primaries),
    'new_primary_pdf_bindings': len(new_pdfs), 'reading_extent_records': len(extents),
    'primary_page_extents': page_count, 'visual_record_identity_bindings': visual_count,
    'copied_controls': controls,
    'limits': 'Parent read full contribution REVIEW, FINAL, REPORT, READING-AND-LIMITS, working derivation and verifier. Source, primary, comparator, original-history bodies and renders were identity-bound only; reviewer semantic/visual coverage remains attributed. No new parent primary retrieval or visual reading, exhaustive clearance, or artifact-based mathematical inference.'
}
for name, value in [('contribution-replay.json', out), ('contribution-observed-root.json', before)]:
    f = P / name
    f.write_text(json.dumps(value, indent=2) + '\n')
    f.chmod(0o600)
print(json.dumps(out, indent=2))
