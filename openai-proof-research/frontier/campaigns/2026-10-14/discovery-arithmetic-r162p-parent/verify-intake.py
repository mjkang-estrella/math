#!/usr/bin/env python3
"""Read-only verification of the sealed no-nominee research handoff."""
from pathlib import Path
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162p-parent'
r=b/'fresh-arithmetic-discovery-r162p';m=r/'packet/private'
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
anchors={'FINAL.md':'618e2c40f085a5fd8ad83d716ad6ca0e30aae6a3317e3469d16e6ca4dc0b9e94',
    'private/MANIFEST.json':'a35f6b8f8d73eeac52bbc56c638015dcdc2c6e49c73ba54bfa731be83ee4fbd4',
    'REPORT.md':'a0e9fdfc6e5a950372f1b46bb353ba8c68fbe41e98c3cdd78210199616dfbb1e'}
for rel,h in anchors.items():assert sha((r/rel).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'packet/public/verify_packet.py'),'packet','--root',str(r),
    '--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['private/MANIFEST.json'],
    '--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'private/MANIFEST.json');assert len(manifest['files'])==70
td=(p/'sources/preprints-tree.json').read_bytes();assert sha(td)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(td);assert len(tree['tree'])==13223 and not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
auth=load(m/'canonical-authentication.json');assert len(auth)==35;by_path={x['path']:x for x in auth}
for x in auth:
    d=(r/x['local']).read_bytes();y=lookup[x['path']]
    assert len(d)==x['bytes']==y['size'] and sha(d)==x['sha256']
    assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
coverage=load(m/'canonical-coverage.json');assert len(coverage)==35
for x in coverage:
    assert x['bytes']==by_path[x['path']]['bytes']
    if not x['pdf_authentication_only']:assert not x['display_range_union_holes']
text_bytes=sum(x['bytes'] for x in coverage if not x['pdf_authentication_only']);assert text_bytes==651044
reads=[json.loads(x) for x in (m/'semantic-reads.jsonl').read_text().splitlines()]
for x in reads:
    d=(r/by_path[x['path']]['local']).read_bytes();assert sha(d)==x['sha256'] and 0<=x['start']<=x['end']<=len(d)
history=[json.loads(x) for x in (m/'history-reads.jsonl').read_text().splitlines()]
for x in history:
    d=(p/x['path']).read_bytes();assert 0<=x['start']<=x['end']<=len(d)
    if 'sha256' in x:assert len(d)==x['bytes'] and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162o-parent/private/next-direct-originals.json');assert len(direct)==6
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
controls=load(m/'copied-control-results.json');assert controls['original_derivation_unchanged']
assert len(controls['results'])==2 and all(x['expected_returncode']==x['actual_returncode'] for x in controls['results'])
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()}
assert snapshot==load(o/'private/root-before.json')
v={'status':'MATCH','anchors':anchors,'verifier_stdout':run.stdout,'payload_files':70,
    'payload_bytes':sum(x['bytes'] for x in manifest['files']),'root_files_modes_unchanged':75,
    'canonical_blobs_against_complete_tree':35,'reported_complete_canonical_text_bytes':text_bytes,
    'canonical_hash_interval_records':len(reads),'history_interval_records':len(history),
    'unique_original_history_hashes':2,'completed_direct_originals_unchanged':6,
    'reading_metadata_is_not_semantic_reading':True,'saved_copied_controls_match':2,'controls_rerun':False,
    'parent_semantically_read':['REPORT.md','FINAL.md','packet/public/verify_packet.py',
        'packet/private/derivation.md','packet/private/READING-LIMITS.md','packet/private/source-understanding.md'],
    'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,
    'clipping_recovery_access_failure_false_admissions_coarse_omissions_preserved':True,
    'parent_missing_verifier_path_corrected_from_own_manifest':True,
    'artifact_scope':'Exact packet file membership,size,hash and anchors; parent separately checks current root byte/mode preservation. No sealed-directory/mode claim.',
    'mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
