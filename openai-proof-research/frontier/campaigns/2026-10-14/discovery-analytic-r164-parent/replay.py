#!/usr/bin/env python3
"""Read-only completed Analytic164 packet intake; no mathematical grade."""
import hashlib, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O = Path(__file__).resolve().parent
B = O.parent
P = B.parents[2]
R = B / 'fresh-analytic-discovery-r164'
spec = importlib.util.spec_from_file_location('helpers', B / 'discovery-analytic-r161-parent/replay.py')
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
sha, snap = h.sha, h.snap
ANCHORS = {'FINAL.md': '5d987c9415c2390651c9bbf52db1742e29504b8b06a71e5fb17b3b4f924dd5ae',
           'MANIFEST.json': '221b542674bee3624faeb0fd4ad9a560ea6bdaa95742bce65634251d2b8d9360',
           'REPORT.md': 'c6e36d75e14382ec2540a93dbdd2450cbc4ab2655cdf9981a5c22de1bb93a60d'}
def read(f): return json.loads(f.read_text())
def dump(n, v): (O / n).write_text(json.dumps(v, indent=2) + '\n')
def main():
    before = snap(R)
    mode = stat.S_IMODE(R.stat().st_mode)
    status = read(O / 'task-status.json')['structuredContent']
    assert status['status'] == 'completed' and status['workState'] == 'result_available'
    assert not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R / n) == value and value in status['summary'] for n, value in ANCHORS.items())
    manifest = read(R / 'MANIFEST.json')
    assert len(manifest['members']) == 79
    assert {e['path'] for e in manifest['members']} == {
        n for n, e in before.items() if e['kind'] == 'file'
        and n.casefold() not in {'manifest.json', 'report.md', 'private/control-results.json', 'private/detached-anchors.json'}
        and not n.casefold().startswith('private/copied-controls/')}
    treepath = P / 'sources/preprints-tree.json'
    assert sha(treepath) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = read(treepath)
    assert len(tree['tree']) == 13223 and not tree['truncated']
    entries = {e['path']: e for e in tree['tree']}
    objects = read(R / 'private/objects.json')
    assert len(objects) == 31
    for e in objects:
        f = P / e['local']; raw = f.read_bytes(); canonical = entries[e['path']]
        assert len(raw) == e['size'] == canonical['size'] and sha(f) == e['sha256']
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == e['sha'] == canonical['sha']
        assert e['raw_url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['path']
    versions = read(R / 'private/primary/versions.json')
    assert len(versions) == 3
    for e in versions:
        f = R / 'private/primary' / (e['name'] + '.html')
        assert len(f.read_bytes()) == e['bytes'] and sha(f) == e['sha256']
        assert sha(f.with_suffix('.txt')) == e['text_sha256']
    originals = read(R / 'private/originals.json'); assert len(originals) == 13
    stable = []
    for e in originals:
        original = P / e['path']; selected = R / e['selected']; raw = original.read_bytes()
        assert selected.read_bytes() == raw[e['start']:e['end']] and sha(selected) == e['selected_sha256']
        if e['start'] == 0 and e['end'] == e['bytes']:
            assert len(raw) == e['bytes'] and sha(original) == e['sha256'] and stat.S_IMODE(original.stat().st_mode) == e['mode']
            stable.append({'path': e['path'], 'sha256': e['sha256']})
    args = [sys.executable, '-I', '-B', str(R / 'private/verify_packet.py'), '--root', str(R),
            '--final', ANCHORS['FINAL.md'], '--manifest', ANCHORS['MANIFEST.json'], '--report', ANCHORS['REPORT.md'], '--project', str(P)]
    result = subprocess.run(args, cwd=P, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, (result.stdout, result.stderr)
    controls = read(R / 'private/CONTROL-RESULTS.json')['controls']
    assert controls['clean_copy']['exit_code'] == controls['restored_copy']['exit_code'] == 0
    assert controls['altered_member']['exit_code'] == controls['deleted_member']['exit_code'] == 1
    assert snap(R) == before and stat.S_IMODE(R.stat().st_mode) == mode
    assert all(sha(P / e['path']) == e['sha256'] for e in stable)
    dump('observed-root.json', {'root': before, 'root_mode': mode})
    dump('replay.json', {'anchors': ANCHORS, 'payload_members': 79, 'source_objects': 31, 'primary_HTML_text_pairs': 3,
                        'selected_original_extents': 13, 'stable_named_originals': stable,
                        'read_only_verifier': {'returncode': result.returncode, 'stdout': result.stdout.strip()},
                        'copied_controls': 'Recorded clean/restored pass and altered/deleted rejection checked; no new mutation suite run.',
                        'root_unchanged': True, 'limits': 'Artifact checks only. Parent read complete FINAL/REPORT/REDUCTIONS/CALCULATIONS/verifier and reading/isolation account. Protected source, primary and original proof bodies were authenticated but not semantically reread by parent. Combined metadata display truncated inside isolation, recovered separately; selected extents table not needed as complete semantic proof reading. Selected payload includes FINAL; manifest excludes controls/envelopes as recorded. Entire root snapshot additionally binds current excluded artifacts.'})
    print(json.dumps({'payload_members': 79, 'source_objects': 31, 'primary_pairs': 3, 'stable_originals': len(stable), 'root_unchanged': True, 'mathematical_gate': False}))
if __name__ == '__main__': main()
