#!/usr/bin/env python3
"""Read-only whole-scope contribution-review intake for Arithmetic156 contribution review r1.
Artifact checks only; they are not mathematical gates."""
import collections, datetime, hashlib, importlib.util, json, stat, subprocess
from pathlib import Path

O = Path(__file__).resolve().parent
A = O.parent                         # discovery-arithmetic-r156-parent
B = A.parent                         # campaigns/2026-10-14
P = B.parents[2]                     # project root
R = B / 'arithmetic-r156-contribution-r1'
AUTHOR = B / 'fresh-arithmetic-discovery-r156'
PROOF = B / 'arithmetic-r156-proof-r1'
sp = importlib.util.spec_from_file_location('base', B / 'discovery-analytic-r168-parent/replay.py')
h = importlib.util.module_from_spec(sp); sp.loader.exec_module(h)
sha, snap = h.sha, h.snap


def read(p): return json.loads(p.read_bytes())
def dump(p, d): p.write_text(json.dumps(d, indent=2) + '\n')
def git_blob(d): return hashlib.sha1(b'blob ' + str(len(d)).encode() + b'\0' + d).hexdigest()


def main():
    anchors = {'FINAL.md': 'b451bd65a6261129e03bf93b46f4f508d1c44e98280c87832f5c1d57f356bac5',
               'MANIFEST.json': '9be781718ef32b0099e93fc10843bf4d455d09f79eea9bb084511cc17202510c',
               'REPORT.md': 'c06c6941c65ae5ce1e85a5c54db34bbd9b620fb36f21eb3db0d0b391bc0e7300'}
    before = snap(R); mode = stat.S_IMODE(R.stat().st_mode)
    author_before = snap(AUTHOR); proof_before = snap(PROOF)
    assert all(sha(R / p) == v for p, v in anchors.items())
    assert (R / 'ANCHORS.sha256').read_text() == ''.join(v + '  ' + k + '\n' for k, v in anchors.items())
    cmd = ['python', '-I', '-B', str(R / 'private/verify_packet.py'), '--root', str(R), '--manifest-sha256', anchors['MANIFEST.json'],
           '--final-sha256', anchors['FINAL.md'], '--report-sha256', anchors['REPORT.md']]
    run = subprocess.run(cmd, cwd=P, text=True, capture_output=True, check=True); assert not run.stderr
    out = json.loads(run.stdout); assert out['artifact_verification'] == 'PASS' and out['errors'] == [] and out['read_only'] and not out['mathematical_gate']
    m = read(R / 'MANIFEST.json'); assert m['format'] == 'arithmetic-r156-contribution-r1-exact-packet-v1' and m['verdict'] == 'TECHNICAL'
    selected = {x['path'] for x in m['files']}; assert len(selected) == len(m['files']) == 102
    for x in m['files']:
        q = R / x['path']; d = q.read_bytes()
        assert len(d) == x['bytes'] and hashlib.sha256(d).hexdigest() == x['sha256'] and stat.S_IMODE(q.stat().st_mode) == x['mode']
    files = {p for p, x in before.items() if x['kind'] == 'file'}
    assert files == selected | {'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256'} and len(files) == 105
    # admitted inputs: frozen theorem, author proof, parent assessment/questions unchanged
    ia = read(R / 'private/input-anchors.json'); assert len(ia) == 11
    for x in ia:
        q = P / x['path']; d = q.read_bytes()
        assert len(d) == x['bytes'] and hashlib.sha256(d).hexdigest() == x['sha256'] and stat.S_IMODE(q.stat().st_mode) == x['mode']
    by = {Path(x['path']).name: x for x in ia}
    FR = '91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c'; AP = 'd9c17da764f4224dd02733a09a84eba9f5c47b6a37481ab68aa9e68d6b042f3e'
    assert by['FROZEN.md']['sha256'] == FR and by['FROZEN.md']['bytes'] == 1912 and by['AUTHOR-PROOF.md']['sha256'] == AP and by['AUTHOR-PROOF.md']['bytes'] == 23878
    assert sha(R / 'private/author/FROZEN.md') == FR and sha(R / 'private/author/AUTHOR-PROOF.md') == AP
    op = read(R / 'private/original-preservation.json'); assert len(op['baseline_comparisons']) == 53 and op['author_exterior_expected_hashes_match']
    assert all(x['bytes_sha256_mode_unchanged'] for x in op['baseline_comparisons'])
    # canonical blobs vs complete pinned tree, exhausting three folders, and vs author copies
    tree = read(P / 'sources/preprints-tree.json'); assert len(tree['tree']) == 13223 and not tree['truncated']
    assert sha(P / 'sources/preprints-tree.json') == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    lookup = {e['path']: e for e in tree['tree']}
    sa = read(R / 'private/source-authentication.json'); assert sa['tree_sha256'] == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(sa['blobs']) == 42
    for x in sa['blobs']:
        d = (P / x['local']).read_bytes(); e = lookup[x['path']]
        assert e['type'] == 'blob' and len(d) == x['bytes'] == e['size'] and hashlib.sha256(d).hexdigest() == x['sha256'] and git_blob(d) == x['git_blob'] == e['sha']
        assert sha(P / x['original']) == x['sha256'] and stat.S_IMODE((P / x['original']).stat().st_mode) == x['original_mode']
    folders = collections.Counter(x['path'].split('/')[1] for x in sa['blobs'])
    assert dict(folders) == {'A-conditional-abelianity-theorem-for-special-fourfold-pairs-with-a-half-weight-divisor-October-5-2026': 15,
                             'The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026': 12,
                             'Two-step-monodromy-of-special-quasi-projective-varieties-September-24-2026': 15}
    for fo in folders:
        assert {e['path'] for e in tree['tree'] if e['type'] == 'blob' and e['path'].startswith('preprints/' + fo + '/')} == {x['path'] for x in sa['blobs'] if x['path'].split('/')[1] == fo}
    sr = read(R / 'private/source-reading.json'); assert len(sr) == 42
    complete = [x for x in sr if x['status'].startswith('read completely')]; assert len(complete) == 36 and len(sr) - 36 == 6
    for x in complete: assert x['semantic_extents'] == [[0, x['bytes']]] and sha(R / x['copy']) == x['sha256']
    # primary copies vs author originals, and reading extents
    pa = read(R / 'private/primary-authentication.json'); assert len(pa) == 13
    for x in pa: assert sha(R / x['copy']) == x['sha256'] == sha(P / x['original']) and (R / x['copy']).stat().st_size == x['bytes']
    pr = read(R / 'private/primary-reading.json'); assert len(pr) == 6
    for x in pr:
        assert sha(R / x['copy']) == x['sha256'] and (R / x['copy']).stat().st_size == x['bytes']
        for s, e in x['semantic_extents']: assert 0 <= s < e <= x['bytes']
    ue = next(x for x in pr if 'ue1986' in x['copy']); assert ue['semantic_extents'] == [[0, ue['bytes']]]
    # original history intervals, complete-body copies
    hr = read(R / 'private/history-reading.json'); assert len(hr) == 23; whole = 0
    for x in hr:
        q = P / x['path']; assert sha(q) == x['file_sha256']
        with q.open('rb') as f: f.seek(x['start']); d = f.read(x['end'] - x['start'])
        assert len(d) == x['end'] - x['start'] and hashlib.sha256(d).hexdigest() == x['selected_sha256']
        if 'copy' in x: assert sha(R / x['copy']) == x['selected_sha256']; whole += 1
    assert whole == 4 and len(read(R / 'private/history-selected.json')) == 19
    cr = read(R / 'private/control-results.json'); assert [(x['control'], x['expected_exit'], x['actual_exit']) for x in cr['results']] == [('clean', 0, 0), ('altered', 1, 1), ('missing', 1, 1)]
    g = read(R / 'private/guards.json'); assert '*structural*r190*' in g['wildcards'] and g['path_basis'].startswith('full project-relative')
    assert any('proof' in s for s in g['substrings']) or any('proof' in w for w in g['wildcards']), 'other review role not guarded'
    # nothing changed: review root, author root (vs parent intake snapshot), proof review root (vs correctness adoption snapshot)
    assert snap(R) == before and stat.S_IMODE(R.stat().st_mode) == mode
    assert snap(AUTHOR) == author_before == read(A / 'observed-root.json')['root']
    assert snap(PROOF) == proof_before == read(A / 'proof-r1-adoption/observed-root.json')['root']
    dump(O / 'observed-root.json', {'root': before, 'root_mode': mode, 'author_root': author_before, 'proof_review_root': proof_before})
    report = {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'anchors': anchors, 'artifact_only': True,
              'author_verifier_stdout': run.stdout.strip(), 'payload_files': 102, 'exterior_files': 3, 'root_files': 105, 'exact_whole_root_membership': True,
              'input_anchors': 11, 'baseline_comparisons': 53, 'canonical_objects': 42, 'canonical_folders': 3, 'canonical_folder_blobs_exhausted': True,
              'canonical_matches_complete_pinned_tree_and_author_copies': True, 'source_objects_fully_read': 36, 'source_objects_authenticated_only': 6,
              'primary_copies_matching_author_originals': 13, 'primary_texts_read': 6, 'new_primary_ue1986_complete': True, 'history_reading_units': 23,
              'history_whole_body_copies': whole, 'copied_controls': 3, 'review_root_unchanged': True, 'author_root_unchanged_since_parent_intake': True,
              'proof_review_root_unchanged_since_correctness_adoption': True,
              'parent_finite_rechecks': 'Riemann-Hurwitz 2g(C\')-2=N(2g(C)-2+m/2)>0 for g(C)>=2; I2 components A,B with A^2=-2 from (A+B).A=0 and A.B=2, no (-1)-curve; monodromy coinvariants of T_delta^2 give 2Z delta, local handles give Z delta; Z^8=direct sum of four Z^2 killed coordinatewise',
              'parent_semantic_reading': 'Complete REVIEW, FINAL, REPORT and manifest contract; verifier read. Source/primary/history operative reading attributed to the independent reviewer. The completed proof-review packet was not reread for this adoption beyond its snapshot. Structural190 live body/status/activity/findings not read or steered before its own terminal notification.'}
    dump(O / 'replay.json', report)
    print(json.dumps({k: report[k] for k in ['payload_files', 'canonical_objects', 'history_reading_units', 'review_root_unchanged', 'author_root_unchanged_since_parent_intake', 'proof_review_root_unchanged_since_correctness_adoption']}))


if __name__ == '__main__':
    main()
