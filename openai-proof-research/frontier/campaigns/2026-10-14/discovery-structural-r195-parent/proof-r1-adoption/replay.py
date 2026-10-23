#!/usr/bin/env python3
"""Read-only packet replay and exact original bindings; no mathematical gate."""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

P = Path(__file__).resolve().parent
C = P.parent.parent
PROJECT = C.parents[2]
R = C / 'structural-r195-proof-r1'
A = C / 'fresh-structural-discovery-r195'

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def identity(p): return {'size': p.stat().st_size, 'sha256': sha(p), 'mode': stat.S_IMODE(p.stat().st_mode)}
def snap(root):
    assert not any(p.is_symlink() for p in root.rglob('*'))
    return {str(p.relative_to(root)): identity(p) for p in root.rglob('*') if p.is_file()}

def verify(root, anchors):
    return subprocess.run([sys.executable, '-I', '-B', str(R / 'verify_packet.py'), '--root', str(root),
                           '--final-sha', anchors['FINAL.md'], '--manifest-sha', anchors['MANIFEST.json'],
                           '--report-sha', anchors['REPORT.md']], capture_output=True, text=True, timeout=30)

def main():
    before = snap(R)
    author_before = snap(A)
    anchors = read(P / 'task-status.json')['detached_anchors']
    assert read(R / 'ANCHORS.json')['sha256'] == anchors
    assert all(sha(R / n) == h for n, h in anchors.items())
    v = verify(R, anchors)
    assert v.returncode == 0, (v.stdout, v.stderr)
    manifest = read(R / 'MANIFEST.json')
    assert len(manifest['files']) == 59 and manifest['total_bytes'] == 1247335
    frozen = read(P.parent / 'resume-verification.json')['frozen']
    assert sha(A / 'FROZEN.md') == frozen['sha256']
    assert sha(A / 'AUTHOR-PROOF.md') == frozen['author_proof_sha256']
    baseline = read(R / 'private/input-baseline.json')
    changes = read(R / 'private/final-input-recheck.json')['observed_parent_change']
    assert len(changes) == 1
    changed = changes[0]
    assert changed['path'].endswith('discovery-structural-r195-parent/assessment.md')
    for rel, original in baseline.items():
        expected = changed['final'] if rel == changed['path'] else original
        assert identity(PROJECT / rel) == expected, rel
    tree = read(PROJECT / 'sources/preprints-tree.json')
    assert not tree['truncated'] and len(tree['tree']) == 13223
    lookup = {e['path']: e for e in tree['tree']}
    sources = read(R / 'private/source-bindings.json')
    assert len(sources) == 12
    for row in sources:
        path = row['path']
        e = lookup[path]
        local = A / row['local']
        b = local.read_bytes()
        assert len(b) == row['bytes'] == e['size']
        assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == row['git_blob'] == e['sha']
        assert sha(local) == row['sha256']
        assert row['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + path
        if not path.endswith('.pdf'):
            copy = R / row['local'].replace('private/source/', 'private/selected-source/', 1)
            assert copy.read_bytes() == b
    folder = sources[0]['path'].rsplit('/', 1)[0] + '/'
    assert {x['path'] for x in sources} == {k for k, e in lookup.items() if k.startswith(folder) and e['type'] == 'blob'}
    primary = read(R / 'private/primary-bindings.json')
    assert len(primary) == 7
    for row in primary:
        for kind in ('pdf', 'txt'):
            x = row[kind]
            assert identity(PROJECT / x['path']) == {'size': x['bytes'], 'sha256': x['sha256'], 'mode': x['mode']}
    selected = read(R / 'private/primary-selected-extents.json')
    assert len(selected) == 13
    for x in selected:
        src = PROJECT / x['source']
        if 'start' not in x:
            assert src.suffix == '.png' and sha(src) == sha(R / x['copy']) == x['sha256']
            continue
        assert sha(src) == x['source_sha256']
        with src.open('rb') as f:
            f.seek(x['start']); b = f.read(x['end'] - x['start'])
        assert (R / x['copy']).read_bytes() == b
        assert sha(R / x['copy']) == x['copy_sha256']
    history = read(R / 'private/history-bindings.json')
    assert len(history) == 9
    for x in history:
        src = PROJECT / x['path']
        with src.open('rb') as f:
            f.seek(x['start']); b = f.read(x['end'] - x['start'])
        assert b.startswith(x['heading'].encode()) and hashlib.sha256(b).hexdigest() == x['sha256']
        assert (R / x['copy']).read_bytes() == b
    control = R / 'private/controls/tiny'
    ca = {n: sha(control / n) for n in anchors}
    controls = []
    with tempfile.TemporaryDirectory(prefix='s195-proof-controls-', dir=P) as td:
        dest = Path(td) / 'tiny'
        shutil.copytree(control, dest)
        def check(name, expected, aa=ca):
            result = verify(dest, aa)
            assert (result.returncode == 0) == expected, (name, result.stderr)
            controls.append({'case': name, 'accepted': result.returncode == 0})
        check('intact copied fixture', True)
        for name in ('payload.txt', 'FINAL.md', 'MANIFEST.json', 'REPORT.md'):
            p = dest / name; b = p.read_bytes(); p.write_bytes(b + b'!')
            check('changed ' + name, False); p.write_bytes(b)
        p = dest / 'extra.txt'; p.write_text('x'); check('extra file', False); p.unlink()
        p = dest / 'payload.txt'; b = p.read_bytes(); p.unlink(); check('missing payload', False); p.write_bytes(b)
        check('wrong REPORT anchor', False, {**ca, 'REPORT.md': '0' * 64})
    assert snap(R) == before and snap(A) == author_before
    result = {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'artifact_only': True, 'anchors': anchors, 'verifier_stdout': v.stdout.strip(),
              'selected_files': 59, 'selected_bytes': 1247335, 'source_blobs': 12,
              'selected_source_texts': 11, 'primary_pairs': 7, 'primary_text_extents': 11, 'primary_renders': 2,
              'history_extents': 9, 'baseline_inputs': len(baseline),
              'parent_assessment_change_disclosed_and_current_bytes_matched': True,
              'copied_controls': controls, 'review_and_author_roots_unchanged': True,
              'frozen': frozen, 'review_sha256': sha(R / 'REVIEW.md')}
    (P / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('anchors', 'frozen')}, indent=2))

if __name__ == '__main__': main()
