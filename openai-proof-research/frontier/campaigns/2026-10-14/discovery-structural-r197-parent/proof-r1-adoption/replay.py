#!/usr/bin/env python3
"""Read-only correctness-packet replay; only copied tiny fixtures are mutated.

This authenticates artifacts and recorded reading extents, not mathematical
truth or whether a human/agent actually read an authenticated passage.
"""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile

P = Path(__file__).resolve().parent
C = P.parents[1]
PROJECT = C.parents[2]
R = C / 'structural-r197-proof-r1'
K = R / 'packet'
A = C / 'fresh-structural-discovery-r197'
AK = A / 'packet'
read = lambda p: json.loads(p.read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
anchors = {
    'FINAL': 'bb124ebc0e6eeb3fd68772493e8cc566bd3ea53f227329d42766fc989c158e9d',
    'MANIFEST': 'd41edd97b608eb7ec015180d14df0a97b3c3066582617c7760282991eed93ae3',
    'REPORT': '9f3538b50469e5e70b752eef93f87f53fa6212f4d148e9833c1abe87a83590c1',
}

def inventory(root):
    result = {}
    for p in [root, *root.rglob('*')]:
        s = p.lstat()
        assert not p.is_symlink()
        assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)
        e = {'mode': stat.S_IMODE(s.st_mode), 'kind': 'dir' if p.is_dir() else 'file'}
        if p.is_file():
            e.update(bytes=s.st_size, sha256=sha(p.read_bytes()))
        result[p.relative_to(root).as_posix()] = e
    return result

def bounded_bytes(path, start, end):
    assert 0 <= start <= end <= path.stat().st_size
    with path.open('rb') as f:
        f.seek(start)
        b = f.read(end - start)
    assert len(b) == end - start
    return b

def verify(root, a):
    return subprocess.run(
        [sys.executable, '-I', '-B', str(K / 'verify_packet.py'), '--root', str(root),
         '--final-sha256', a['FINAL'], '--manifest-sha256', a['MANIFEST'],
         '--report-sha256', a['REPORT']], capture_output=True, text=True, timeout=20)

before = inventory(R)
author_before = inventory(A)
assert author_before == read(P.parent / 'observed-root.json')
recorded_author = read(K / 'private/author-integrity-before.json')
actual_author_files = {k: v for k, v in author_before.items() if v['kind'] == 'file'}
assert set(actual_author_files) == {e['path'] for e in recorded_author}
for e in recorded_author:
    x = actual_author_files[e['path']]
    assert (x['bytes'], x['sha256'], x['mode']) == (e['bytes'], e['sha256'], int(e['mode'], 8))
after_record = read(K / 'private/author-integrity-after.json')
assert after_record['files'] == 83
assert after_record['before_sha256'] == sha((K / 'private/author-integrity-before.json').read_bytes())

v = verify(R, anchors)
assert v.returncode == 0, (v.stdout, v.stderr)
vr = json.loads(v.stdout)
assert (vr['files'], vr['directories']) == (86, 13)
manifest = read(R / 'MANIFEST.json')
detached = read(R / 'DETACHED.json')
for name, h in anchors.items():
    assert detached[name] == h
for name, key in [('STATEMENT.txt', 'reviewed_statement'), ('AUTHOR-PROOF.txt', 'reviewed_author_proof')]:
    b = (AK / name).read_bytes()
    assert b == (K / 'private/frozen-inputs' / name).read_bytes()
    assert sha(b) == detached[key]

tb = (PROJECT / 'sources/preprints-tree.json').read_bytes()
assert sha(tb) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tb)
assert not tree['truncated'] and len(tree['tree']) == 13223
prefix = 'preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/'
selection = [e for e in tree['tree'] if e['path'].startswith(prefix)]
retained_tree = read(K / 'private/source-tree.json')
assert sorted(selection, key=lambda e: e['path']) == sorted(retained_tree, key=lambda e: e['path'])
lookup = {e['path']: e for e in selection if e['type'] == 'blob'}
records = read(K / 'private/reading-records.json')
assert len(selection) == 13 and len(lookup) == 10
assert set(lookup) == {e['canonical_path'] for e in records['source']}
for e in records['source']:
    b = (K / e['local_path']).read_bytes()
    assert b == (PROJECT / e['original_read_path']).read_bytes()
    assert sha(b) == e['sha256'] and len(b) == e['bytes'] == lookup[e['canonical_path']]['size']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == e['git_blob'] == lookup[e['canonical_path']]['sha']
    if e['semantic_review_read']:
        assert e['read_extent'] == [0, len(b)]
    else:
        assert e['canonical_path'].endswith('.pdf') and e['read_extent'] is None

for e in records['primary_text']:
    p = K / e['text_file']
    assert sha(p.read_bytes()) == e['sha256']
    assert p.read_bytes() == (AK / e['text_file']).read_bytes()
    for start, end in e['read_bytes']:
        bounded_bytes(p, start, end)
for e in records['primary_visual']:
    b = (K / e['path']).read_bytes()
    assert sha(b) == e['sha256'] and b == (AK / e['path']).read_bytes()
extractions = read(K / 'private/primary-extraction.json')
for e in extractions:
    assert sha((PROJECT / e['original_pdf']).read_bytes()) == e['sha256']
    assert e['returncode'] == 0 and e['matches_author_extraction']
    original_text = (PROJECT / e['original_pdf']).with_suffix('.txt')
    assert original_text.read_bytes() == (PROJECT / e['extraction']).read_bytes()

history = read(K / 'private/history-reads.json')
author_history = read(AK / 'private/history-read-extents.json')
assert len(history) == len(author_history) == 20
for i, e in enumerate(history):
    ah = author_history[i]
    assert (e['original'], e['bytes'], e['sha256']) == (ah['path'], ah['bytes'], ah['selected_sha256'])
    b = bounded_bytes(PROJECT / e['original'], *e['bytes'])
    assert sha(b) == e['sha256']
    assert b == (K / 'private/history-selected' / f'{i:02d}.txt').read_bytes()
    assert b == (AK / ah['retained_file']).read_bytes()
for e in read(K / 'private/direct-reads.json'):
    p = PROJECT / e['path']
    assert len(p.read_bytes()) == e['bytes'] and sha(p.read_bytes()) == e['sha256']
    assert stat.S_IMODE(p.stat().st_mode) == int(e['mode'], 8)
limit = read(K / 'private/access-limit.json')
assert sha(bounded_bytes(PROJECT / 'frontier/NEW-TEN-2026-10-14.md', 4801, 6347)) == 'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
brief = C / 'expanded-target-2026-10-17/structural-r197-proof-r1-brief.txt'
assert sha(brief.read_bytes()) == '7e50b4cd577038d2631ca3d00cc730d5c852a3167dcc83e7f30b8d566c3b94f4'

base = R / 'controls/base'
ca = {'FINAL': sha((base / 'packet/FINAL.txt').read_bytes()),
      'MANIFEST': sha((base / 'MANIFEST.json').read_bytes()),
      'REPORT': sha((base / 'REPORT.txt').read_bytes())}
controls = []
with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=P) as td:
    w = Path(td) / 'root'
    def check(name, mutate=None, wrong=None, expected=1):
        if w.exists():
            shutil.rmtree(w)
        shutil.copytree(base, w)
        if mutate:
            mutate(w)
        snap = inventory(w)
        result = verify(w, wrong or ca)
        assert result.returncode == expected, (name, result.stdout, result.stderr)
        assert inventory(w) == snap
        controls.append({'case': name, 'expected_accept': expected == 0,
                         'actual_accept': result.returncode == 0,
                         'verifier_result': json.loads(result.stdout)})
    def change_bytes(w):
        p = w / 'packet/body.txt'
        b = p.read_bytes()
        p.chmod(0o600)
        p.write_bytes(b'X' + b[1:])
        p.chmod(0o444)
    check('clean', expected=0)
    check('bytes', change_bytes)
    check('mode', lambda w: (w / 'packet/body.txt').chmod(0o600))
    check('missing', lambda w: (w / 'packet/body.txt').unlink())
    check('extra-file', lambda w: (w / 'packet/extra.txt').write_text('extra'))
    check('extra-directory', lambda w: (w / 'packet/extra-dir').mkdir())
    for key in ['FINAL', 'MANIFEST', 'REPORT']:
        check(key.lower() + '-anchor', wrong={**ca, key: '0' * 64})
reported = read(K / 'ARTIFACT-CONTROLS.json')['results']
assert [(e['case'], e['actual_accept']) for e in controls] == [(e['case'], e['actual_accept']) for e in reported]
assert inventory(R) == before and inventory(A) == author_before
out = {
    'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'artifact_only': True, 'anchors': anchors, 'verification': vr,
    'selected_files': 86, 'selected_directories': 13,
    'selected_bytes': sum(e['bytes'] for e in manifest['files']),
    'review_sha256': sha((K / 'REVIEW.txt').read_bytes()),
    'review_bytes': (K / 'REVIEW.txt').stat().st_size,
    'root_files': sum(e['kind'] == 'file' for e in before.values()),
    'author_root_files': len(actual_author_files), 'canonical_blobs': 10,
    'primary_texts': len(records['primary_text']), 'primary_images': len(records['primary_visual']),
    'primary_extraction_receipts': len(extractions), 'history_spans': len(history),
    'direct_inputs': 8, 'controls': controls,
    'author_and_reviewer_bytes_modes_unchanged': True,
    'acceptance_span_checked_by_seek_read': True,
    'reviewer_access_lapse_preserved': limit,
    'scope': 'Exact packet, detached anchors and separate root inventories. Binding checks do not independently establish semantic reading or mathematical truth.',
}
(P / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
(P / 'observed-root.json').write_text(json.dumps(before, indent=2) + '\n')
print(json.dumps(out, indent=2))
