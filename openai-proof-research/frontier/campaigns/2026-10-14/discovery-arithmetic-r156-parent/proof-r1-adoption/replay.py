#!/usr/bin/env python3
"""Read-only whole-scope correctness-review intake for Arithmetic156 proof review r1.
Artifact checks only; they are not mathematical gates."""
import collections, datetime, hashlib, importlib.util, json, stat, subprocess
from pathlib import Path

O = Path(__file__).resolve().parent
A = O.parent                         # discovery-arithmetic-r156-parent
B = A.parent                         # campaigns/2026-10-14
P = B.parents[2]                     # project root
R = B / 'arithmetic-r156-proof-r1'
AUTHOR = B / 'fresh-arithmetic-discovery-r156'
sp = importlib.util.spec_from_file_location('base', B / 'discovery-analytic-r168-parent/replay.py')
h = importlib.util.module_from_spec(sp); sp.loader.exec_module(h)
sha, snap = h.sha, h.snap


def read(p): return json.loads(p.read_bytes())
def dump(p, d): p.write_text(json.dumps(d, indent=2) + '\n')
def git_blob(d): return hashlib.sha1(b'blob ' + str(len(d)).encode() + b'\0' + d).hexdigest()


def main():
    anchors = {'FINAL.md': '7113f8fb8cb121c93269d03f0ae9345b1dca5b8bb2034c5ebaebf34d5a3094b6',
               'MANIFEST.json': '39a63b3e5a365b267c06c5e564791d0e5ccb58ba5bec8aa6c5b2049b6f1917ca',
               'REPORT.md': '0a97f872efc6a0c2955775ffccc47b187d2da42a511dbb6092d0e9b5fa11826b'}
    before = snap(R); mode = stat.S_IMODE(R.stat().st_mode)
    author_before = snap(AUTHOR)
    assert all(sha(R / p) == v for p, v in anchors.items())
    assert (R / 'ANCHORS.sha256').read_text() == ''.join(v + '  ' + k + '\n' for k, v in anchors.items())
    # author verifier, read-only, with project originals
    cmd = ['python', '-I', '-B', str(R / 'verify_packet.py'), str(R), '--final-sha', anchors['FINAL.md'],
           '--manifest-sha', anchors['MANIFEST.json'], '--report-sha', anchors['REPORT.md'], '--project', str(P)]
    run = subprocess.run(cmd, cwd=P, text=True, capture_output=True, check=True); assert not run.stderr
    out = json.loads(run.stdout); assert out == {'artifact_consistent': True, 'selected_files': 95, 'explicit_original_checks': 79, 'mathematical_gate': False}
    # exact packet membership and modes
    m = read(R / 'MANIFEST.json'); assert m['format'] == 'r156-review-exact-packet-v1'
    selected = {x['path'] for x in m['files']}; assert len(selected) == len(m['files']) == 95
    for x in m['files']:
        q = R / x['path']; d = q.read_bytes()
        assert len(d) == x['bytes'] and hashlib.sha256(d).hexdigest() == x['sha256'] and stat.S_IMODE(q.stat().st_mode) == x['mode']
    files = {p for p, x in before.items() if x['kind'] == 'file'}
    assert files == selected | {'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256'} and len(files) == 98
    # input anchors: frozen theorem and author proof bytes/modes unchanged
    ia = read(R / 'private/input-anchors.json'); assert len(ia) == 20
    for x in ia:
        q = P / x['path']; d = q.read_bytes()
        assert len(d) == x['bytes'] and hashlib.sha256(d).hexdigest() == x['sha256'] and stat.S_IMODE(q.stat().st_mode) == x['mode']
    by = {Path(x['path']).name: x for x in ia}
    assert by['FROZEN.md']['sha256'] == '91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c' and by['FROZEN.md']['bytes'] == 1912
    assert by['AUTHOR-PROOF.md']['sha256'] == 'd9c17da764f4224dd02733a09a84eba9f5c47b6a37481ab68aa9e68d6b042f3e' and by['AUTHOR-PROOF.md']['bytes'] == 23878
    # 79 explicit original checks, independently
    oc = read(R / 'private/original-checks.json'); assert len(oc) == 79; whole = 0
    for x in oc:
        q = P / x['path']
        with q.open('rb') as f:
            if 'start' in x: f.seek(x['start']); d = f.read(x['bytes'])
            else: d = f.read(); whole += 1
        assert len(d) == x['bytes'] and hashlib.sha256(d).hexdigest() == x['sha256']
        if 'mode' in x: assert stat.S_IMODE(q.stat().st_mode) == x['mode']
    assert whole == 75
    # canonical blobs against the complete pinned tree, exhausting three folders
    tree = read(P / 'sources/preprints-tree.json'); assert len(tree['tree']) == 13223 and not tree['truncated']
    assert sha(P / 'sources/preprints-tree.json') == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    lookup = {e['path']: e for e in tree['tree']}
    auth = read(R / 'private/authentication.json'); assert len(auth) == 42
    for x in auth:
        d = (R / x['path']).read_bytes(); e = lookup[x['canonical']]
        assert e['type'] == 'blob' and len(d) == x['bytes'] == e['size'] and hashlib.sha256(d).hexdigest() == x['sha256'] and git_blob(d) == x['git_blob'] == e['sha']
    folders = collections.Counter(x['canonical'].split('/')[1] for x in auth)
    tv = read(R / 'private/tree-verification.json'); assert dict(folders) == tv['folder_counts'] == {
        'A-conditional-abelianity-theorem-for-special-fourfold-pairs-with-a-half-weight-divisor-October-5-2026': 15,
        'The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026': 12,
        'Two-step-monodromy-of-special-quasi-projective-varieties-September-24-2026': 15}
    for fo in folders:
        all_blobs = {e['path'] for e in tree['tree'] if e['type'] == 'blob' and e['path'].startswith('preprints/' + fo + '/')}
        assert all_blobs == {x['canonical'] for x in auth if x['canonical'].split('/')[1] == fo}
    sr = read(R / 'private/source-reading.json'); st = collections.Counter(x['status'] for x in sr)
    assert len(sr) == 42 and st['complete semantic reading'] == 36 and sum(st.values()) - 36 == 6
    for x in sr:
        if x['status'] == 'complete semantic reading': assert x['semantic_extents'] == [[0, x['bytes']]]
    # original-history intervals vs copies
    oi = read(R / 'private/original-intervals.json'); assert len(oi) == 4
    for x in oi:
        with (P / x['path']).open('rb') as f: f.seek(x['start']); d = f.read(x['end'] - x['start'])
        assert len(d) == x['end'] - x['start'] and hashlib.sha256(d).hexdigest() == x['sha256'] == sha(R / x['copy'])
    # primary copies and independent acquisitions
    pr = read(R / 'private/primary-reading.json'); assert len(pr) == 5
    for x in pr:
        assert (R / x['path']).stat().st_size == x['bytes'] and sha(R / x['path']) == x['sha256']
        if x['complete']: assert x['semantic_extents_bytes_half_open'] == [[0, x['bytes']]]
    ind = read(R / 'private/primary-independent/acquisition.json'); assert len(ind) == 3
    for x in ind:
        q = R / 'private/primary-independent' / (x['name'] + '.pdf'); assert q.stat().st_size == x['bytes'] and sha(q) == x['sha256']
        assert x['same_as_author_pdf'] and sha(q) == sha(R / 'private/primary' / (x['name'] + '.pdf'))
    cr = read(R / 'private/control-results.json'); assert [(x['case'], x['expected_exit'], x['actual_exit']) for x in cr] == [('clean', 0, 0), ('corrupt', 1, 1), ('missing', 1, 1)]
    g = read(R / 'private/guards.json'); assert any('*structural*r190*' == w for w in g['wildcards']) and any('r156-contribution' in w or 'contribution' in w for w in g['wildcards'] + g['substrings'] + g.get('extra_patterns', []))
    # nothing changed
    assert snap(R) == before and stat.S_IMODE(R.stat().st_mode) == mode
    assert snap(AUTHOR) == author_before
    author_obs = read(A / 'observed-root.json')['root']
    assert author_obs == author_before, 'author root differs from parent intake snapshot'
    dump(O / 'observed-root.json', {'root': before, 'root_mode': mode, 'author_root': author_before})
    report = {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'anchors': anchors, 'artifact_only': True,
              'author_verifier_stdout': run.stdout.strip(), 'payload_files': 95, 'exterior_files': 3, 'root_files': 98,
              'exact_whole_root_membership': True, 'input_anchors': 20, 'explicit_original_checks': 79, 'whole_original_checks': whole,
              'canonical_objects': 42, 'canonical_folders': 3, 'canonical_folder_blobs_exhausted': True, 'canonical_matches_complete_pinned_tree': True,
              'source_objects_fully_read': 36, 'source_objects_authenticated_only': 6, 'history_intervals': 4, 'primary_copies': 5,
              'primary_complete': sum(1 for x in pr if x['complete']), 'independent_primary_acquisitions': 3, 'copied_controls': 3,
              'review_root_unchanged': True, 'author_root_unchanged_since_parent_intake': True,
              'parent_finite_rechecks': 'a=(34), b=(13)(24), c=(12)(34): a,b involutions, ab of order 4, [a,b]=(ab)^2=c, <a,b> of order 8 containing c, c^(m+1)=1 for odd m; Riemann-Hurwitz g(C\')=1+N(g-1)+Nm/4 integral for (N,m)=(2,even),(8,odd); (T_delta^2-I)Z^2=2Z delta; I2 model q2=e z3^2+f z4^2 splits into two planes meeting q1 in conics smooth iff d-cf/e!=0, meeting at the two points z3=z4=0, a z1^2+b z2^2=0',
              'parent_semantic_reading': 'Complete REVIEW, FINAL, REPORT, UNRESOLVED, verifier and the parent questions.md; private DERIVATIONS/READING openings. Source/primary/history operative reading attributed to the independent reviewer. No live Arithmetic156 contribution review or Structural190 bodies/status/activity/findings read or steered.'}
    dump(O / 'replay.json', report)
    print(json.dumps({k: report[k] for k in ['payload_files', 'explicit_original_checks', 'canonical_objects', 'source_objects_fully_read', 'review_root_unchanged', 'author_root_unchanged_since_parent_intake']}))


if __name__ == '__main__':
    main()
