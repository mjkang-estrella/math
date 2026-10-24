#!/usr/bin/env python3
"""Read-only correctness packet binding; mutate only tiny parent-local controls."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, tempfile

P = Path(__file__).resolve().parent
C = P.parent
PROJECT = C.parents[2]
A = C / 'fresh-structural-discovery-r209'
R = C / 'structural-r209-proof-r1'
read = lambda p: json.loads(p.read_bytes())
sha = lambda b: hashlib.sha256(b).hexdigest()
anchors = {
    'FINAL': '281c4555d90a1d48272035187f49b491931c2317dc7d5b2b94002c994fba7326',
    'MANIFEST': '31e63c70149c06e26127b914d1b6e0c4423f1699ab012e46147682628a449cff',
    'REPORT': '6f7c261e32a587bfc03f46e9fb01094a6cc52c162f1bae3b03615d43415cb7a3',
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
assert sha((R / 'verify_packet.py').read_bytes()) == '86637293bb73fa760ecab5dcadf1c0a01cb00c97571a51a34e556b1573d6711d'
v = run(R / 'verify_packet.py', R, anchors)
assert v.returncode == 0, (v.stdout, v.stderr)
av = run(A / 'verify_packet.py', A, read(P / 'replay.json')['anchors'])
assert av.returncode == 0, (av.stdout, av.stderr)
tb = (PROJECT / 'sources/preprints-tree.json').read_bytes()
assert sha(tb) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = {e['path']: e for e in json.loads(tb)['tree']}
sources = read(R / 'private/source-authentication.json')
assert len(sources) == 16
canon = {e['path']: e for e in read(A / 'private/authenticated-source.json')}
formal = {e['path']: e for e in read(A / 'private/lean-authentication.json')}
for e in sources:
    if e['path'] in canon:
        old = canon[e['path']]
        assert all(e[k] == old[k] for k in ['path', 'local', 'bytes', 'sha256', 'git_blob'])
        p = A / e['local']
        t = tree[e['path']]
        assert e['git_blob'] == t['sha'] and e['bytes'] == t['size']
    else:
        old = formal[e['path']]
        assert all(e[k] == old[k] for k in ['path', 'bytes', 'sha256', 'git_blob'])
        p = A / 'private' / Path(e['path']).name
    b = p.read_bytes()
    assert len(b) == e['bytes'] and sha(b) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == e['git_blob']
primaries = read(R / 'private/primary-authentication.json')
assert len(primaries) == 14
for e in primaries:
    p = A / e['path']
    assert p.is_relative_to(A) and p.relative_to(A).as_posix() in author_before
    b = p.read_bytes()
    assert len(b) == e['bytes'] and sha(b) == e['sha256']

history = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/proof.md'
history_spans = {(0, 929), (3544, 11553)}
author_prefix = A.relative_to(PROJECT).as_posix() + '/'

def admitted_bytes(path, lo, hi):
    assert isinstance(lo, int) and isinstance(hi, int) and 0 <= lo <= hi
    if path.startswith(author_prefix):
        rel = path[len(author_prefix):]
        assert rel in author_before and author_before[rel]['type'] == 'file'
        assert hi <= author_before[rel]['bytes']
    elif path == history:
        assert (lo, hi) in history_spans
    else:
        assert path == 'sources/preprints-tree.json' and lo == 0 and hi == len(tb)
    with (PROJECT / path).open('rb') as f:
        f.seek(lo)
        b = f.read(hi - lo)
    assert len(b) == hi - lo
    return b

logs = [json.loads(x) for x in (R / 'private/read-log.jsonl').read_text().splitlines()]
for e in logs:
    assert sha(admitted_bytes(e['path'], e['start'], e['end'])) == e['sha256']
coverage = read(R / 'private/semantic-coverage.json')['coverage']
extents = renders = 0
for e in coverage:
    if 'bytes' in e:
        lo, hi = e['bytes']
        admitted_bytes(e['path'], lo, hi)
        extents += 1
        if 'pdf_page_one_based' in e:
            assert e['path'].startswith(author_prefix + 'private/primary/') and e['path'].endswith('.txt')
            b = (PROJECT / e['path']).read_bytes()
            pages = b.split(b'\x0c')
            page = e['pdf_page_one_based'] - 1
            offset = sum(len(p) + 1 for p in pages[:page])
            assert offset <= lo <= hi <= offset + len(pages[page])
    else:
        assert e['path'].startswith(author_prefix + 'private/primary/') and e['path'].endswith('.png')
        rel = e['path'][len(author_prefix):]
        assert rel in author_before
        renders += 1
assert sha((R / 'private/acceptance.txt').read_bytes()) == 'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'

controls = []
with tempfile.TemporaryDirectory(prefix='proof-controls-', dir=P) as tmp:
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
    'author_verification': json.loads(av.stdout),
    'review_files': sum(e['type'] == 'file' for e in before.values()),
    'review_directories': sum(e['type'] == 'directory' for e in before.values()),
    'author_files_unchanged': 85, 'review_originals_unchanged': True,
    'canonical_blob_bindings': 14, 'formal_bindings': 2, 'primary_file_bindings': len(primaries),
    'logged_extent_hash_bindings': len(logs), 'semantic_extent_metadata_bindings': extents,
    'render_integrity_only': renders, 'copied_controls': controls,
    'limits': 'Parent read the complete review, FINAL, REPORT, reading limits and working reasoning, and inspected the verifier code. Source, primary, original-history, comparator and render evidence was identity-bound only here. Reviewer semantic/visual coverage remains attributed to the reviewer. No fresh primary retrieval, inherited semantic reading, formal proof coverage or contribution decision is claimed.'
}
for name, value in [('proof-replay.json', out), ('proof-observed-root.json', before)]:
    p = P / name
    p.write_text(json.dumps(value, indent=2) + '\n')
    p.chmod(0o600)
print(json.dumps(out, indent=2))
