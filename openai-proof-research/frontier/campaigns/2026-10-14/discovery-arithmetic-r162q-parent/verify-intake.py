#!/usr/bin/env python3
"""Read-only research artifact/input checks; assigns no mathematical gate."""
from pathlib import Path
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162q-parent'
r=b/'fresh-arithmetic-discovery-r162q';m=r/'packet/private'
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
anchors={'FINAL.md':'220732d7a123cc63ac22cd6c610da3d5771729eb5effbfc5b7b0efb17856ed84',
    'MANIFEST.json':'b41d7beb932a7e42ceca1967cafaf404d6da78a3342c7d9115aa8845bb39ecf4',
    'REPORT.md':'e27933266bbc9e279fc0fcbf6634a1e4cb715979856ccb8336e67094e7347494'}
for rel,h in anchors.items():assert sha((r/rel).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'verify_packet.py'),'--root',str(r),
    '--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],
    '--report-sha',anchors['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'MANIFEST.json');assert len(manifest['files'])==42
td=(p/'sources/preprints-tree.json').read_bytes();assert sha(td)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(td);assert len(tree['tree'])==13223 and not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
auth=load(m/'canonical-auth.json');assert len(auth)==14
for x in auth:
    d=(r/x['local']).read_bytes();y=lookup[x['path']]
    assert len(d)==x['bytes']==y['size'] and sha(d)==x['sha256']
    assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['bytes'] for x in auth if not x['path'].endswith('.pdf'))==189302
primary=load(m/'primary-objects.json')['objects']
for x in primary:
    d=(r/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162p-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
with (p/'frontier/iterations/i27-geometric-analysis-discovery.md').open('rb') as f:
    f.seek(15044);history=f.read(33437-15044)
assert history==(m/'history-i27.txt').read_bytes()
controls=load(r/'packet/own/controls/observed.json')
assert controls['same_copy_accepted'] and controls['changed_copy_rejected'] and controls['original_unchanged']
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()}
assert snapshot==load(o/'private/root-before.json')
v={'status':'MATCH','anchors':anchors,'verifier_stdout':run.stdout,'payload_files':42,
    'payload_bytes':sum(x['bytes'] for x in manifest['files']),'root_files_modes_unchanged':45,
    'canonical_blobs_against_complete_tree':14,'reported_complete_canonical_text_bytes':189302,
    'primary_object_bindings':len(primary),'completed_direct_originals_unchanged':4,
    'selected_original_history_span_comparisons':1,'history_span':[15044,33437],
    'metadata_is_not_semantic_reading':True,'saved_copied_control_cases_match':2,'controls_rerun':False,
    'parent_semantically_read':['REPORT.md','FINAL.md','verify_packet.py','packet/private/derivation.md',
        'packet/private/source-understanding.md','packet/private/READING-LIMITS.md'],
    'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,
    'late_reads_false_admissions_encoding_format_recovery_coarse_omissions_retained':True,
    'artifact_scope':'Exact root file boundary,payload sizes/hashes and detached anchors; parent separately checks current byte/mode preservation. No sealed-directory/mode claim.',
    'mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
