#!/usr/bin/env python3
"""Read-only completed exact-selection and unchanged-input checks; no math gate."""
from pathlib import Path
import hashlib
import json
import subprocess

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ah'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    result={}
    for p in root.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();result[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return result
before=json.loads((D/'private/intake/root-before.json').read_text());assert len(before)==11 and snapshot(R)==before
anchors={'FINAL.md':'768ad0beb85c816a12fc158b4a5fa4d7d573adf5a18c5bddb726e3dc2560720d','MANIFEST.json':'f99def0b60f9b9ff4c0de3c034b84cad6eedd7d2f51b97577de0443a666b3235','REPORT.md':'30bad922b87f1fb380c77e4ab0a9ea044de00e26418df7e8798862d45e7b9003'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
checked=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True)
manifest=json.loads((R/'MANIFEST.json').read_text());members={x['path'] for x in manifest['files']}
assert len(members)==8 and sum(x['bytes'] for x in manifest['files'])==38254
assert set(before)==members|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==43
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
old_roots={}
for round_id,n in [('r162af',54),('r162ag',12)]:
    old=D.parent/f'fresh-arithmetic-discovery-{round_id}'
    prior=json.loads((D.parent/f'discovery-arithmetic-{round_id}-parent/private/intake/root-before.json').read_text())
    assert len(prior)==n and snapshot(old)==prior;old_roots[round_id]=n
assert snapshot(R)==before
result=dict(status='MATCH',exact_manifest_files=8,manifest_bytes=38254,whole_root_files=11,whole_root_bytes_and_full_modes_unchanged=True,parent_exact_membership_checked=True,completed_direct_inputs_unchanged=43,old_roots_files_unchanged=old_roots,tiny_copied_own_text_controls=2,synthetic_mutations_not_rerun=True,detached_anchors=anchors,verifier_output=checked.stdout.strip(),verifier_limits='Child checks selected bytes,three anchors and unchanged/one-byte-changed own-text copies; not exact filesystem membership,modes,mathematics,external provenance or complete ancestry. Parent checks exact membership and pre-read bytes/full modes of11 current files,43 admitted originals,and both previous roots.',parent_reading='Complete new handoff,scope,notebook,reading limits and records; original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
