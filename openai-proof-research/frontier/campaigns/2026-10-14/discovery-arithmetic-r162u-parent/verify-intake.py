#!/usr/bin/env python3
"""Read-only artifact/input authentication; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162u-parent';r=b/'fresh-arithmetic-discovery-r162u';m=r/'packet/private';sha=lambda d:hashlib.sha256(d).hexdigest();load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'b7b7d3549d2a87eb1cb055894cb0450c4c21ecccea8cb0ef3036ee9cb4572792','MANIFEST.json':'ae6447162c794d3fa3b5bfe0883a402a16abccb2e7f1692da5b829aad1f457ae','REPORT.md':'ed1a173e595b09a73376893ef6990c1a28081485e126e32ff0c088f74fb984a3'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'verify_packet.py'),'--root',str(r),'--final-sha',a['FINAL.md'],'--manifest-sha',a['MANIFEST.json'],'--report-sha',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'MANIFEST.json');files={k:x for k,x in manifest['inventory'].items() if x['kind']=='file'};dirs=sum(x['kind']=='directory' for x in manifest['inventory'].values());assert len(files)==64 and dirs==13
raw=(p/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223;lookup={x['path']:x for x in tree['tree']}
selection=load(m/'canonical-tree-selection.json');assert len(selection)==17
for x in selection:assert x==lookup[x['path']]
auth=load(m/'canonical-authentication.json');assert len(auth)==12
for x in auth:
 d=(p/x['local']).read_bytes();y=lookup[x['path']];assert len(d)==x['size']==y['size'] and sha(d)==x['sha256'];assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['size'] for x in auth if not x['path'].endswith('.pdf'))==151824
primary=load(m/'primary/access.json');bound=0
for x in primary:
 if 'sha256' not in x:assert 'error' in x;continue
 rows=[(k,z) for k,z in files.items() if k.startswith('private/primary/') and z['sha256']==x['sha256']];assert len(rows)==1
 d=(r/'packet'/rows[0][0]).read_bytes();assert len(d)==x.get('size',x.get('bytes')) and sha(d)==x['sha256'];bound+=1
assert bound==4
receipts=load(m/'authorized-reading-receipts.json');assert len(receipts)==13
for x in receipts:
 start,end=x['byte_extent']
 with (p/x['source']).open('rb') as f:f.seek(start);d=f.read(end-start)
 assert d==(r/x['copy']).read_bytes() and len(d)==x['bytes'] and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162t-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
with (p/'sources/CONTENTS.md').open('rb') as f:f.seek(142501);d=f.read(143682-142501)
assert d==(m/'source085-catalogue.txt').read_bytes()
controls=load(m/'artifact-checks.json');assert controls['originals_unchanged'] and len(controls['results'])==5 and all(x['matched_expectation'] and (x['returncode']==0)==x['expected_acceptance'] for x in controls['results'])
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()};assert snapshot==load(o/'private/root-before.json') and len(snapshot)==73
v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':64,'payload_bytes':sum(x['bytes'] for x in files.values()),'packet_directories_including_root':dirs,'root_files_modes_unchanged':73,'canonical_blobs_against_complete_tree':12,'canonical_selection_entries':17,'reported_complete_canonical_text_blobs':11,'reported_complete_canonical_text_bytes':151824,'primary_acquisition_bindings':4,'primary_payload_files':sum(k.startswith('private/primary/') for k in files),'failed_primary_version_retrieval_disclosed':1,'completed_direct_originals_unchanged':4,'authorized_original_span_receipts_checked':13,'selected_original_history_receipts':6,'saved_copied_control_cases_match':5,'controls_rerun':False,'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','verify_packet.py','packet/private/derivation.md','packet/private/source-understanding.md','packet/private/primary-understanding.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'late_scope_boundary_confirmation_clipping_recovery_access_failure_false_admissions_coarse_omissions_retained':True,'artifact_scope':'Exact payload file/directory membership, modes, sizes, hashes, verifier identity and detached anchors; entire current root full-mode/byte preservation separately checked. No mathematical gate.','mathematical_gate_assigned':False,'accepted':False,'count_change':0};(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
