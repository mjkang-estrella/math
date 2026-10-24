#!/usr/bin/env python3
"""Read-only completed-packet and admitted-input checks; no mathematical gate."""
from pathlib import Path
import hashlib
import json
import runpy

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ag'
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    result={}
    for p in root.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();result[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return result
before=json.loads((D/'private/intake/root-before.json').read_text())
assert snapshot(R)==before
anchors={'FINAL.md':'3c8248e2ae1f94b5106f190da2afa49fc388c759ae47029ef63221ed31d72d3d','MANIFEST.json':'f099cfa07369b25461a8dae84fd514d3e76fab4a57565db80ca3ac3e00460d31','REPORT.md':'d80e2e5b0ac0e255e943a70b0d45dfe66190b45d64a1f1fb50bef7033e7f1c1e'}
v=runpy.run_path(str(R/'verify.py'))['check'](R,anchors['FINAL.md'],anchors['MANIFEST.json'],anchors['REPORT.md'])
assert v['artifact_check']=='PASS' and v['files']==9 and v['bytes']==39366 and v['mathematical_gate'] is False
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==36
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
old=D.parent/'fresh-arithmetic-discovery-r162af'
old_before=json.loads((D.parent/'discovery-arithmetic-r162af-parent/private/intake/root-before.json').read_text())
assert len(old_before)==54 and snapshot(old)==old_before
controls=json.loads((R/'packet/private/copied-controls/outcomes.json').read_text())
assert controls['copied_bytes']==120 and controls['mathematical_gate'] is False
assert controls['own_original_unchanged_sha256']==sha((R/'packet/private/scope.md').read_bytes())
assert [(x['case'],x['observed']) for x in controls['controls']]==[('intact','accept'),('copied-byte','reject'),('extra-file','reject'),('final-anchor','reject'),('manifest-anchor','reject'),('report-anchor','reject')]
assert snapshot(R)==before
result=dict(status='MATCH',exact_manifest_files=9,manifest_bytes=39366,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,completed_direct_inputs_unchanged=36,old_r162af_root_files_unchanged=54,saved_control_outcomes_checked=6,saved_controls_not_rerun=True,detached_anchors=anchors,verifier_limits='Child verifier checks bytes/exact membership and rejects symlink/path escapes; no modes,mathematics,external provenance or complete ancestry. Parent compares12 current root files,36 exact readonly inputs and54 old root files in bytes/full modes. No new canonical downloads or binding reauthentication claimed.',parent_reading='Complete new handoff,scope,notebook,reading limits and records; original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
