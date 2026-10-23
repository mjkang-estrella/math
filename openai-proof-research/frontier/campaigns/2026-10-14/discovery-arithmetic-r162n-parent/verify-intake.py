#!/usr/bin/env python3
"""Read-only sealed research verification, separate from mathematical gates."""
from pathlib import Path
import hashlib
import json
import subprocess

p=Path.cwd()
b=p/'frontier/campaigns/2026-10-14'
o=b/'discovery-arithmetic-r162n-parent'
r=b/'fresh-arithmetic-discovery-r162n'
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
def snapshot(root):
    return {f.relative_to(root).as_posix():{'bytes':f.stat().st_size,
        'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}
anchors={'FINAL.md':'53ee03d84642d0519b090efa02bc676cbb5ec5d649f6b7d4ea7bd57823303c5b',
    'MANIFEST.json':'86dddf62cc412cc5d4b67c8473d05ef8a2a4a6d84bc7d910004dcb63c09052ed',
    'REPORT.md':'cf4cb50fb60f02b51cc864cc8ba06bcdafccd4b3e37082a8c4f2743ce4a712fd'}
for rel,h in anchors.items():assert sha((r/rel).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'packet/verify.py'),'--root',str(r),
    '--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],
    '--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'MANIFEST.json')
assert len(manifest['files'])==66 and len(manifest['directories'])==24
td=(p/'sources/preprints-tree.json').read_bytes()
assert sha(td)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(td);assert len(tree['tree'])==13223 and not tree['truncated']
lookup={x['path']:x for x in tree['tree']}
auth=load(r/'packet/private/canonical-authentication.json');assert len(auth)==21
for x in auth:
    d=(p/x['local']).read_bytes();y=lookup[x['path']]
    assert len(d)==x['size']==y['size'] and sha(d)==x['sha256']
    assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
originals=load(r/'packet/private/original-read-extents.json');assert len(originals)==9
for x in originals:
    d=(p/x['path']).read_bytes()
    assert len(d)==x['bytes'] and sha(d)==x['sha256']
    assert x['semantic_extent']==[0,len(d)]
primary=load(r/'packet/private/primary-object-digests.json')
for x in primary:
    d=(r/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
controls=load(r/'packet/ARTIFACT-CONTROLS.json')
assert len(controls['cases'])>=3
assert snapshot(r)==load(o/'private/root-before.json')
v={'status':'MATCH','anchors':anchors,'verifier_stdout':run.stdout,
    'payload_files':66,'payload_bytes':sum(x['bytes'] for x in manifest['files']),
    'directories':24,'root_files_unchanged':69,'canonical_blobs_against_complete_tree':21,
    'semantic_canonical_reading_reported':'19 non-PDF/non-vendor objects; full operative chain before calculations',
    'primary_object_bindings':len(primary),'completed_original_whole_hash_comparisons':9,
    'copied_control_cases_checked_from_saved_record':len(controls['cases']),
    'controls_rerun':False,'parent_semantically_read':['REPORT.md','FINAL.md','packet/RESEARCH.md',
        'packet/verify.py','packet/private/derivation.md','packet/private/READING-LIMITS.md',
        'packet/private/source-understanding.md'],
    'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,
    'false_admissions_coarse_omissions_late_reads_recoveries_preserved':True,
    'artifact_checks_assign_mathematical_gate':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps(v,indent=2))
