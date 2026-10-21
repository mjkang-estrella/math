#!/usr/bin/env python3
"""Parent contribution intake: current bytes, not mathematical gates."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

OUT = Path(__file__).resolve().parent
BASE = OUT.parent.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 't185r144-contribution-r1'
AUTHOR = BASE / 'fresh-structural-discovery-r144'
spec = importlib.util.spec_from_file_location('intake_helpers', OUT.parent / 'replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': 'ec3c3f4ffecd52f4485bd3f38e03caccd09c04aba490cbfe0d1d4e630afc031e',
    'MANIFEST.json': 'ce4a911b820f020498a42fa1eea99a02ff829a70405762622f1f2de873ad86e4',
    'REPORT.md': '30162f5d670b8f5088ec8a3a16a058baf0912e3f3334afbd1d8ad52fca2d9c8f',
}


def dump(n, v):
    (OUT / n).write_text(json.dumps(v, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    assert all(sha(PROJECT / p) == h for p, h in helper.PROTECTED.items())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 481, 'task_index': 480,
         'protected_unrelated_sha256': helper.PROTECTED})
    before, author_before = snap(ROOT), snap(AUTHOR)
    assert author_before == json.loads((OUT.parent / 'observed-root.json').read_text())['root']
    dump('observed-roots.json', {'observed_utc': now, 'review_root': before,
         'author_root': author_before, 'limits': 'Present complete roots; author also matches its earlier parent intake observation. No historical OS/whole-parent certificate.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    m = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert m['schema'] == 't185r144-contribution-r1-exact-v1'
    assert {p for p, e in before.items() if e['kind'] == 'file'} == {e['path'] for e in m['files']} | set(m['outer_files'])
    assert {p for p, e in before.items() if e['kind'] == 'directory'} == set(m['directories'])
    for e in m['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['bytes']
    incoming = ROOT / 'private/incoming/author'
    omitted = {'private/controls/contribution-r1-disposition.md'}
    author_files = {p for p, e in author_before.items() if e['kind'] == 'file'}
    assert {p for p, e in snap(incoming).items() if e['kind'] == 'file'} == author_files - omitted
    assert all(sha(incoming / p) == sha(AUTHOR / p) for p in author_files - omitted)
    assert sha(incoming / 'notes/03-frozen-scope.md') == helper.SCOPE
    assert sha(incoming / 'notes/04-author-proof.md') == helper.PROOF
    tp = PROJECT / 'sources/preprints-tree.json'
    assert sha(tp) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tp.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    entries = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'private/controls/source-authentication.json').read_text())
    for e in sources:
        p = PROJECT / e['retained_path']
        assert p.is_relative_to(ROOT)
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == e['bytes'] == entries[e['canonical_path']]['size']
        assert blob == e['git_blob'] == entries[e['canonical_path']]['sha']
        assert sha(p) == e['sha256'] and e['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    pdf_checks = 0
    for e in json.loads((incoming / 'private/primary/receipts.json').read_text()):
        p = incoming / 'private/primary' / (e['name'] + '.pdf')
        assert sha(p) == e['sha256'] and p.stat().st_size == e['bytes']
        pdf_checks += 1
    for e in json.loads((ROOT / 'private/primary/reuse-receipts.json').read_text()):
        assert sha(PROJECT / e['retained_pdf']) == e['sha256']
        assert sha(ROOT / 'private/primary' / (e['name'] + '-review-extract.txt')) == e['review_extract_sha256']
        assert sha(incoming / 'private/primary' / (e['name'] + '.txt')) == e['retained_text_sha256'] == e['review_extract_sha256']
    axioms = json.loads((ROOT / 'private/primary/axioms-receipt.json').read_text())
    assert sha(ROOT / 'private/primary/axioms-v3.pdf') == axioms['sha256']
    assert (ROOT / 'private/primary/axioms-v3.pdf').stat().st_size == axioms['bytes']
    assert sha(ROOT / 'private/primary/axioms-v3.txt') == axioms['text_sha256']
    pdf_checks += 1
    originals = json.loads((ROOT / 'private/controls/current-originals.json').read_text())['records']
    for e in originals:
        assert sha(PROJECT / e['original']) == e['current_sha256'] == e['snapshot_sha256']
        snapshot = PROJECT / e['snapshot'] if 'snapshot' in e else ROOT / 'private/history' / e['original']
        assert sha(snapshot) == e['snapshot_sha256']
    cases = []
    with tempfile.TemporaryDirectory(prefix='t185-contribution-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'packet'
        shutil.copytree(ROOT, copy)
        args = [str(copy), '--manifest-sha256', ANCHORS['MANIFEST.json'],
                '--final-sha256', ANCHORS['FINAL.md'], '--report-sha256', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            r = subprocess.run([sys.executable, '-B', str(copy / 'tools/verify.py'), *(custom or args)],
                               capture_output=True, text=True, timeout=30)
            assert (r.returncode == 0) == expected, (label, r.stdout, r.stderr)
            assert snap(copy) == state
            cases.append(dict(case=label, expected_pass=expected, returncode=r.returncode,
                              fixture_unchanged=True, stdout=r.stdout.strip(), stderr=r.stderr.strip()))

        check('baseline', True)
        p = copy / 'notes/01-contribution-assessment.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_payload', False)
        p.unlink()
        check('missing_payload', False)
        p.write_bytes(b)
        p = copy / '.extra-control.json'
        p.write_text('{}')
        check('extra_hidden_payload', False)
        p.unlink()
        wrong = args.copy()
        wrong[4] = '0' * 64
        check('wrong_external_final_anchor', False, wrong)
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before and snap(AUTHOR) == author_before
    assert all(sha(PROJECT / e['original']) == e['current_sha256'] for e in originals)
    assert all(sha(PROJECT / p) == h for p, h in helper.PROTECTED.items())
    dump('copied-controls.json', {'cases': cases, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'review_and_author_roots_unchanged': True,
         'limits': 'Current complete copied-review byte checks only, not mathematical gates.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_review_anchors': ANCHORS, 'frozen_scope_sha256': helper.SCOPE, 'author_proof_sha256': helper.PROOF,
         'payload_files': len(m['files']), 'whole_review_files': sum(e['kind'] == 'file' for e in before.values()),
         'whole_author_files': len(author_files), 'matching_reduced_author_copy_files': len(author_files - omitted),
         'declared_omitted_author_copy_files': sorted(omitted), 'canonical_source185_blobs': len(sources),
         'primary_pdf_file_checks': pdf_checks, 'operative_primary_versions': 3, 'matching_reused_text_extractions': 2,
         'selected_current_originals': originals, 'stable_selected_inputs': len(originals),
         'artifact_cases': 6, 'negative_cases': 4, 'review_and_author_roots_unchanged': True,
         'earlier_author_intake_snapshot_matches': True, 'selected_originals_unchanged_over_execution': True,
         'protected_unrelated_files_unchanged': True,
         'limits': 'Artifact/current selected-byte evidence only. Reduced author snapshot is not a complete packet; no independent correctness gate, fresh full primary/history reading, historical OS/whole-parent or priority certificate.'})
    print(json.dumps({'payload_files': len(m['files']), 'source185_blobs': len(sources),
                      'primary_pdf_file_checks': pdf_checks, 'stable_inputs': len(originals),
                      'artifact_cases': 6, 'negative_cases': 4, 'whole_roots_unchanged': True}))


if __name__ == '__main__':
    main()
