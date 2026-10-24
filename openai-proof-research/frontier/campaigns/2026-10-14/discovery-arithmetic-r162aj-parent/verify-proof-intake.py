#!/usr/bin/env python3
"""Verify the fixed review/input selection read-only; never assign a math gate."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = D.parent / 'arithmetic-r162aj-proof-r1'

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def snapshot(root):
    result = {}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw = f.read_bytes()
            result[f.relative_to(root).as_posix()] = dict(
                bytes=len(raw), sha256=sha(raw), mode=f.stat().st_mode)
    return result

before = json.loads((D/'private/proof-intake/root-before.json').read_text())
assert len(before) == 37 and snapshot(R) == before
anchors = {
    'FINAL.md': '59adcdfdd59e81c7dd7a159a773f778af9261425728122e4aaa8d2d7d40bcc24',
    'MANIFEST.json': '0b5afa4cf89b155668a8a0621959de338ea915fcb12caccda9cc44acf29473d2',
    'REPORT.md': '92396960ebea53ed6bee685cb12fe2ae1b7d6af934542ebb785f00553d29e1a5',
}
for name, expected in anchors.items():
    assert sha((R/name).read_bytes()) == expected
m = json.loads((R/'MANIFEST.json').read_text())
assert len(m['artifacts']) == 34 and len(m['readonly_inputs']) == 73
assert set(before) == {
    (P/x['path']).relative_to(R).as_posix() for x in m['artifacts']
} | {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
admitted = {x['path']:x for x in json.loads((D/'private/review-inputs.json').read_text())}
assert len(admitted) == 79
extras = {'AGENTS.md','sources/upstream.json','sources/preprints-tree.json',
          'frontier/NEW-TEN-2026-10-14.md'}
assert all(x['path'] in admitted or x['path'] in extras for x in m['readonly_inputs'])
assert [x.get('range') for x in m['readonly_inputs'] if 'range' in x] == [[4801,6347]]
for x in m['readonly_inputs']:
    if x['path'] in admitted:
        f=P/x['path']; raw=f.read_bytes(); a=admitted[x['path']]
        assert len(raw)==a['bytes']==x['bytes']
        assert sha(raw)==a['sha256']==x['sha256']
        assert f.stat().st_mode==a['mode']
        assert oct(stat.S_IMODE(f.stat().st_mode))==x['mode']
cmd=['python','-I','-B',str(R/'verify.py'),
     '--final-sha256',anchors['FINAL.md'],
     '--manifest-sha256',anchors['MANIFEST.json'],
     '--report-sha256',anchors['REPORT.md']]
checked=subprocess.run(cmd,cwd=P,capture_output=True,text=True,check=True)
assert '34 artifacts; 73 readonly inputs; 3 copied controls' in checked.stdout
author=D.parent/'fresh-arithmetic-discovery-r162aj'
old=json.loads((D/'private/intake/root-before.json').read_text())
assert len(old)==91 and snapshot(author)==old
contribution=D.parent/'arithmetic-r162aj-contribution-r1'
cb=json.loads((D/'private/contribution-intake/root-before.json').read_text())
assert len(cb)==17 and snapshot(contribution)==cb
assert snapshot(R)==before
result=dict(
    status='MATCH', manifest_artifacts=34,
    artifact_bytes=sum(x['bytes'] for x in m['artifacts']),
    readonly_input_objects_checked=73, admitted_author_objects_checked=69,
    exact_review_root_files=37, review_bytes_and_full_modes_unchanged=True,
    author_root_files_unchanged=91, contribution_root_files_unchanged=17,
    copied_controls_checked=3, synthetic_mutations_not_rerun=True,
    journal_input_extent_half_open=[4801,6347], detached_anchors=anchors,
    child_verifier_stdout=checked.stdout,
    verifier_limits='Child checks selected artifacts, inputs, anchors and copied controls; parent additionally checks exact whole review membership and full modes, author and contribution roots. No directory-identity or mathematical verdict follows.',
    parent_reading='Complete REVIEW characters [0,16000),[16000,32499); complete FINAL,REPORT,READING-LIMITS,verifier and working notes. Two oversized metadata displays clipped metadata only; all input references subsequently validated programmatically. Parent did not independently reread upstream or primary proofs.',
    no_foreign_live_queries=True, no_new_research_dispatch=True,
    artifact_check_only=True, count_change=0)
(D/'proof-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
