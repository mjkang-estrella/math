#!/usr/bin/env python3
"""Parent authentication for the unchanged review; no mathematical/novelty gate."""
from pathlib import Path
import hashlib
import json
import re
import runpy
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
PROJECT = PARENT.parents[3]
REVIEW = PARENT.parent / 't165p135-contribution-r1'
AUTHOR = PARENT.parent / 'fresh-structural-discovery-r135'
ANCHORS = {
    'FINAL.json': '5e1bfd30b75d26d465e2be2143cb9649650602cb49129197e8aec4e050a5a23b',
    'MANIFEST.json': '0ab0a068109be758529d2e38708779d79d6231dda73599153cd3c5debab9bf67',
    'REPORT.md': '6de14a2e669e5636b9ee1799d8ef48a9ed70aeec09493ff2095b87f9cd48c510',
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
snapshot = runpy.run_path(str(PARENT / 'replay.py'))['snapshot']

def verify(root, anchors):
    for rel, expected in anchors.items():
        if sha(root / rel) != expected:
            raise ValueError('external anchor mismatch: ' + rel)
    final = json.loads((root / 'FINAL.json').read_text())
    if final['review_manifest_sha256'] != anchors['MANIFEST.json']:
        raise ValueError('FINAL manifest binding')
    files = json.loads((root / 'MANIFEST.json').read_text())['files']
    for rel, h in files.items():
        p = Path(rel)
        if p.is_absolute() or '..' in p.parts or (root / p).is_symlink():
            raise ValueError('unsafe sealed path: ' + rel)
        if sha(root / p) != h:
            raise ValueError('sealed payload mismatch: ' + rel)
    actual = {str(p.relative_to(root)) for p in (root / 'packet/public').rglob('*') if p.is_file()}
    expected = {p for p in files if p.startswith('packet/public/')}
    if actual != expected:
        raise ValueError('public payload file-set mismatch')
    return len(files)

def main():
    author_before, review_before = snapshot(AUTHOR), snapshot(REVIEW)
    assert author_before == json.loads((PARENT / 'original-snapshot.json').read_text())
    count = verify(REVIEW, ANCHORS)
    deps = {}
    for line in (REVIEW / 'work/input-hashes.txt').read_text().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        if match:
            h, rel = match.groups()
            assert sha(PROJECT / rel) == h, rel
            deps[rel] = h
    listed_count = len(deps)
    for rel, h in json.loads((PARENT / 'replay.json').read_text())['external_dependencies'].items():
        assert sha(PROJECT / rel) == h, rel
        deps[rel] = h
    tree_path = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_path) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_path.read_text())
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    blobs = {e['path']: e for e in tree['tree'] if e['type'] == 'blob'}
    companion = REVIEW / 'scratch/complete-graphs-companion'
    sources = json.loads((companion / 'receipts.json').read_text())
    for r in sources:
        data = (companion / r['path'].replace('/', '__')).read_bytes()
        blob = hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()
        e = blobs[r['path']]
        assert blob == e['sha'] == r['git_blob_sha1'] == r['tree_sha1']
        assert len(data) == e['size'] == r['size']
        assert hashlib.sha256(data).hexdigest() == r['sha256']
        assert r['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + r['path']
    primaries = json.loads((REVIEW / 'work/acquisition-register.json').read_text())['primary']
    for r in primaries:
        p = REVIEW / r['file']
        assert sha(p) == r['sha256']
        assert sha(p.with_suffix('.txt')) == r['text_sha256']
    cases = []
    with tempfile.TemporaryDirectory(prefix='.review-controls-', dir=HERE) as tmp:
        for case in ['baseline', 'wrong-anchor', 'flip-final', 'flip-manifest', 'flip-report',
                     'flip-review', 'flip-limits', 'missing-review', 'extra-public']:
            root = Path(tmp) / case
            files = set(json.loads((REVIEW / 'MANIFEST.json').read_text())['files']) | {'FINAL.json', 'MANIFEST.json'}
            for rel in files:
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(REVIEW / rel, p)
            targets = {'flip-final': 'FINAL.json', 'flip-manifest': 'MANIFEST.json',
                'flip-report': 'REPORT.md', 'flip-review': 'packet/public/review.md',
                'flip-limits': 'packet/public/reading-limits.md'}
            if case in targets:
                p = root / targets[case]
                p.write_bytes(p.read_bytes() + b'\nparent mutation\n')
            if case == 'missing-review':
                (root / 'packet/public/review.md').unlink()
            if case == 'extra-public':
                (root / 'packet/public/unlisted.txt').write_text('unlisted\n')
            anchors = dict(ANCHORS)
            if case == 'wrong-anchor':
                anchors['FINAL.json'] = '0' * 64
            before = snapshot(root)
            try:
                verify(root, anchors)
                accepted, error = True, None
            except (ValueError, OSError, KeyError) as exc:
                accepted, error = False, str(exc)
            cases.append({'case': case, 'accepted': accepted,
                'as_expected': accepted == (case == 'baseline'),
                'copy_unchanged': before == snapshot(root), 'error': error})
    author_unchanged = author_before == snapshot(AUTHOR)
    review_unchanged = review_before == snapshot(REVIEW)
    deps_unchanged = all(sha(PROJECT / p) == h for p, h in deps.items())
    all_expected = all(c['as_expected'] and c['copy_unchanged'] for c in cases)
    all_expected &= author_unchanged and review_unchanged and deps_unchanged
    record = {'kind': 'PARENT_REVIEW_AUTHENTICATION_NOT_GATE', 'anchors': ANCHORS,
        'manifest_files': count, 'reviewer_sealing_time_input_bindings': listed_count,
        'current_external_original_bindings': deps, 'canonical_companion_bodies': len(sources),
        'primary_pdf_text_pairs_checked': len(primaries), 'copied_cases': cases,
        'whole_author_root_unchanged': author_unchanged, 'whole_review_root_unchanged': review_unchanged,
        'external_originals_unchanged': deps_unchanged, 'all_expected': bool(all_expected),
        'coverage_limits': 'Original review has a12-file hash manifest and author-copy baseline/sanity controls, '
        'not a standalone externally anchored review verifier or review tamper suite. Parent supplies that '
        'authentication and9 copied seal controls; checks6 primary PDF/text pairs and6 canonical companion bodies. '
        'Manifest omits other root/private paths, and reviewer bindings are sealing-time, not a before/after '
        'review-start certificate. Parent whole-root mode/nlink snapshots cover preservation during this replay '
        'only; no syscall-denial, historical-read or portable-release claim.'}
    (HERE / 'replay.json').write_text(json.dumps(record, indent=2) + '\n')
    assert all_expected, record
    print(json.dumps({k: record[k] for k in ['all_expected','manifest_files','reviewer_sealing_time_input_bindings',
        'canonical_companion_bodies','primary_pdf_text_pairs_checked','whole_author_root_unchanged','whole_review_root_unchanged']}))

if __name__ == '__main__':
    main()
