#!/usr/bin/env python3
"""Read-only authentication of the r162bl artifacts; no mathematical gate."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, subprocess

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = D.parent / 'fresh-arithmetic-discovery-r162bl'
A = {
    'FINAL.md': 'b2a237f9b35e04f00fc61e35e4bc00f2630880ae07e7acc6a015793d9fa22818',
    'MANIFEST.json': '8b5e038b4c66d9c8f06142c32d69632ecbcd194514478eb1bfa8ff2536edb209',
    'REPORT.md': 'b3508bcf79c487aacb640e20d2bd94a91bc08fa3b78aec9119d4e8c4f0514d42',
}
def sha(a): return hashlib.sha256(a).hexdigest()
def unique(pairs):
    out = {}
    for k, v in pairs:
        assert k not in out
        out[k] = v
    return out
def read(p): return json.loads(p.read_bytes(), object_pairs_hook=unique)
def snapshot(root):
    out = {}
    for p in root.rglob('*'):
        st = p.lstat()
        assert not stat.S_ISLNK(st.st_mode)
        if stat.S_ISREG(st.st_mode):
            a = p.read_bytes()
            out[p.relative_to(root).as_posix()] = dict(bytes=len(a), sha256=sha(a), mode=st.st_mode)
        else:
            assert stat.S_ISDIR(st.st_mode)
    return out

before = read(D / 'private/intake/root-before.json')
assert snapshot(R) == before
for n, h in A.items(): assert sha((R / n).read_bytes()) == h
run = subprocess.run(['python', '-I', '-B', str(R / 'verify.py'), str(R), *A.values(), '--project', str(P)], cwd=P, capture_output=True, text=True)
assert run.returncode == 0, (run.stdout, run.stderr)
m = read(R / 'MANIFEST.json')
rows = m['files']; names = [e['path'] for e in rows]
assert names == sorted(set(names)) and len({n.casefold() for n in names}) == len(names)
assert set(before) == set(names) | {'MANIFEST.json', 'REPORT.md'}
for e in rows:
    n = e['path']; q = PurePosixPath(n)
    assert not q.is_absolute() and '..' not in q.parts and q.as_posix() == n
    p = R / n; a = p.read_bytes(); st = p.lstat()
    assert stat.S_ISREG(st.st_mode) and st.st_nlink == 1
    assert len(a) == e['bytes'] and sha(a) == e['sha256'] and st.st_mode == int(e['mode'], 8)
dns = [e['path'] for e in m['directories']]
assert dns == sorted(set(dns))
assert set(dns) == {'.'} | {p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']: assert (R / e['path']).stat().st_mode == int(e['mode'], 8)
for n, mode in m['detached_modes'].items(): assert (R / n).stat().st_mode == int(mode, 8)

a = (P / 'sources/preprints-tree.json').read_bytes()
assert len(a) == 4858136 and sha(a) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(a); assert not tree['truncated'] and len(tree['tree']) == 13223
blob_count = 0; entry_count = 0; text_count = 0; text_bytes = 0
for selection, bindings, expected_count in [('tree-selection.json', 'source-bindings.json', 10), ('companion-tree.json', 'companion-bindings.json', 14)]:
    selected = read(R / 'private' / selection)
    folders = [e['path'] for e in selected if e['type'] == 'tree' and e['path'].count('/') == 1]
    assert len(folders) == 1
    expected = [e for e in tree['tree'] if e['path'] == folders[0] or e['path'].startswith(folders[0] + '/')]
    assert len(selected) == len(expected) and {e['path']: e for e in selected} == {e['path']: e for e in expected}
    blobs = {e['path']: e for e in selected if e['type'] == 'blob'}
    auth = read(R / 'private' / bindings)
    assert len(auth) == expected_count and {e['path'] for e in auth} == set(blobs)
    for e in auth:
        b = blobs[e['path']]; p = R / e['local']; a = p.read_bytes()
        assert all(e[k] == b[k] for k in ['mode', 'type', 'sha', 'size'])
        assert len(a) == e['size'] and sha(a) == e['sha256'] and p.stat().st_mode == int(b['mode'], 8)
        assert hashlib.sha1(b'blob ' + str(len(a)).encode() + b'\0' + a).hexdigest() == b['sha']
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['path']
        if not e['path'].endswith('.pdf'): text_count += 1; text_bytes += len(a)
    blob_count += len(blobs); entry_count += len(selected)
assert (blob_count, entry_count, text_count, text_bytes) == (24, 31, 22, 248343)

initial = read(D / 'private/completed-direct-inputs.json')
copies = read(R / 'private/completed-bindings.json')
later = read(R / 'private/completed-later-modes.json')['records']
assert len(initial) == len(copies) == len(later) == 5
for e, c, l in zip(initial, copies, later):
    assert e['path'] == c['path'] == l['path']
    assert e['bytes'] == c['bytes'] and e['sha256'] == c['sha256']
    assert stat.S_IMODE(e['mode']) == int(c['mode'], 8)
    p = P / e['path']; a = p.read_bytes()
    assert len(a) == e['bytes'] and sha(a) == e['sha256'] and p.stat().st_mode == e['mode'] == int(l['full_mode'], 8)
    assert a == (R / c['copy']).read_bytes() and (R / c['copy']).stat().st_mode == int(l['copy_full_mode'], 8)
primaries = [e for e in read(R / 'private/primary/reading-bindings.json') if 'pdf_bytes' in e]
assert len(primaries) == 3
for e in primaries:
    for extension, prefix in [('pdf', 'pdf'), ('txt', 'extract')]:
        a = (R / 'private/primary' / (e['name'] + '.' + extension)).read_bytes()
        assert len(a) == e[prefix + '_bytes'] and sha(a) == e[prefix + '_sha256']

ns = {'__name__': 'artifact_readonly', '__file__': str(R / 'verify.py')}
exec(compile((R / 'verify.py').read_bytes(), str(R / 'verify.py'), 'exec'), ns)
controls = []
for name in A:
    bad = dict(A); bad[name] = '0' * 64
    try: ns['verify'](R, bad, project=P)
    except ValueError as ex:
        assert 'anchor mismatch' in str(ex)
        controls.append('wrong ' + name + ' anchor REJECTED')
    else: raise AssertionError('Wrong anchor accepted')
tiny = R / 'private/tiny-control'
tiny_result = ns['verify'](tiny, {n: sha((tiny / n).read_bytes()) for n in A}, project=P)
assert tiny_result['result'] == 'MATCH'
assert snapshot(R) == before
out = dict(status='MATCH', scope='Artifact authentication only; no mathematical gate', bundled_verifier_passed=True, bundled_verifier_stdout=run.stdout.strip(), payload_records=len(rows), payload_bytes=sum(e['bytes'] for e in rows), whole_root_files=len(before), directories_including_root=len(dns), detached_anchors=A, duplicate_keys_rejected=True, exact_membership_hashes_lengths_full_modes_matched=True, source_tree_entries=entry_count, source_blobs=blob_count, canonical_text_objects=text_count, canonical_text_bytes=text_bytes, primary_pdfs_and_extracts_independently_verified=3, initial_completed_original_and_copy_pairs=5, author_initial_context_full_modes_recorded=False, author_initial_context_permission_bits_matched=True, parent_predispatch_ledger_original_full_modes_matched=True, mode_record_limitation_preserved=True, controls=controls, restored_tiny_control=tiny_result, whole_root_bytes_and_full_modes_unchanged=True)
(D / 'verification.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out))
