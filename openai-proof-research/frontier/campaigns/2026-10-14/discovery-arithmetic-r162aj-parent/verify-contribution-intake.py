#!/usr/bin/env python3
"""Read-only selected review/input verification; no correctness gate or count."""
from pathlib import Path
import hashlib
import json
import subprocess

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'arithmetic-r162aj-contribution-r1'
def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot(root):
    out={}
    for p in root.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return out
before=json.loads((D/'private/contribution-intake/root-before.json').read_text());assert len(before)==17 and snapshot(R)==before
anchors={'FINAL.md':'c3c2cd4cb5f942e9b4c1f928cea2c308e75def432d44bfc13bde03f288ba6d05','MANIFEST.json':'7291173231dd0d04106cb54157d46e2582a044e764e3ec04c5cbc51ec7d97ce2','REPORT.md':'a4fc52b4b6cef1d6fa2ad032a8ac791beed95d7ecd782aff2f9d91916265b6bf'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
m=json.loads((R/'MANIFEST.json').read_text());assert len(m['files'])==13
assert set(before)=={x['path'] for x in m['files']}|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
admitted={x['path']:x for x in json.loads((D/'private/review-inputs.json').read_text())};assert len(admitted)==79
inputs=json.loads((R/'private/inputs.json').read_text())['items'];assert len(inputs)==45
extras={'AGENTS.md','sources/upstream.json','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md'}
assert all(x['path'] in admitted or x['path'] in extras for x in inputs)
for x in inputs:
    if x['path'] in admitted:
        p=P/x['path'];raw=p.read_bytes();a=admitted[x['path']]
        assert len(raw)==a['bytes']==x['bytes'] and sha(raw)==a['sha256']==x['sha256'] and p.stat().st_mode==a['mode']
    if x['path']=='frontier/NEW-TEN-2026-10-14.md':assert x['extent_half_open']==[4801,6347]
checked=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md'],'--inputs'],cwd=P,capture_output=True,text=True,check=True)
v=json.loads(checked.stdout);assert v['payload_files']==13 and v['input_objects_checked']==45 and v['mathematical_gate'] is False
author=D.parent/'fresh-arithmetic-discovery-r162aj';old=json.loads((D/'private/intake/root-before.json').read_text());assert len(old)==91 and snapshot(author)==old
c=json.loads((R/'private/CONTROL-RESULTS.json').read_text());assert c['matching_copy_matches'] and c['single_byte_change_detected']
assert sha((R/c['matching_copy']).read_bytes())==c['expected_sha256'] and sha((R/c['changed_copy']).read_bytes())!=c['expected_sha256']
assert snapshot(R)==before
result=dict(status='MATCH',exact_manifest_files=13,manifest_bytes=sum(x['bytes'] for x in m['files']),whole_review_root_files=17,whole_review_root_bytes_and_full_modes_unchanged=True,parent_exact_root_membership_checked=True,selected_readonly_input_objects_checked=45,author_root_files_unchanged=91,pre_dispatch_author_input_selection=79,copied_controls_checked=2,synthetic_mutations_not_rerun=True,detached_anchors=anchors,verifier_limits='Child checks named selected bytes/permission modes,3 anchors and45 inputs including ONLY the1546-byte journal interval;does not recursively establish root membership,directory identities or mathematics. Parent checks exact17-file root membership/pre-read full modes and unchanged91-file author root against pre-review snapshot.',parent_reading='Full40222-character review read in contiguous[0,18000),[18000,36000),[36000,end) intervals;complete handoff,limits and working notes. Original source/primary proofs not independently reread by parent.',other_review_status_or_body_not_queried=True,correctness_gate=None,count_change=0)
(D/'contribution-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
