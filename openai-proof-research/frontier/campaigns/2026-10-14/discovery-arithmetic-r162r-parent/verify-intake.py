#!/usr/bin/env python3
"""Read-only artifact checks; no mathematical gate or count assignment."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162r-parent';r=b/'fresh-arithmetic-discovery-r162r';m=r/'packet/private'
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'c527a85fa0607c1f712a21b8c97cac16ae935c01bd5e0f0b7fadcfebbb7b48c7','private/MANIFEST.json':'27933b3b965a62df08f9555bcc5947dec891717af9f6bde4250271f5ac0df98a','REPORT.md':'406f747e9f7bcd8b39bd5b8ccd74c030b0120a8c7083192fb3b8beb4b2b432ac'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'verify_packet.py'),'--root',str(r),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['private/MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'private/MANIFEST.json');assert len(manifest['entries'])==69
td=(p/'sources/preprints-tree.json').read_bytes();assert sha(td)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(td);assert len(tree['tree'])==13223 and not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
auth=load(m/'canonical-authentication.json');assert len(auth)==39
selection=load(m/'canonical-tree-selection.json');assert len(selection)==50
for x in selection:assert x==lookup[x['path']]
for x in auth:
 d=(r/x['local']).read_bytes();y=lookup[x['path']];assert len(d)==x['bytes']==y['size'] and sha(d)==x['sha256'];assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['bytes'] for x in auth if not x['path'].endswith('.pdf'))==244578
primary=load(m/'primary-local-objects.json')
for x in primary:
 d=(r/x['local']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162q-parent/private/next-direct-originals.json');assert len(direct)==4
for x in load(m/'direct-input-receipts.json'):
 with (p/x['path']).open('rb') as f:
  if 'extent' in x:f.seek(x['extent'][0]);d=f.read(x['extent'][1]-x['extent'][0])
  else:d=f.read()
 assert len(d)==x['bytes'] and sha(d)==x['sha256']
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
assert (p/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r35/scope.json').read_bytes()==(m/'history-r35-scope.json').read_bytes()
controls=load(m/'controls/results.json');print('SAVED CONTROLS',json.dumps(controls))
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()}
assert snapshot==load(o/'private/root-before.json') and len(snapshot)==73
v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':69,'payload_bytes':sum(x['bytes'] for x in manifest['entries']),'root_files_modes_unchanged':73,'canonical_blobs_against_complete_tree':39,'canonical_selection_entries':50,'reported_complete_canonical_text_blobs':36,'reported_complete_canonical_text_bytes':244578,'primary_object_bindings':len(primary),'completed_direct_originals_unchanged':4,'direct_input_receipts_checked':9,'selected_original_history_scope_comparisons':1,'saved_copied_control_results':controls,'controls_rerun':False,'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','verify_packet.py','packet/private/derivation.md','packet/private/source-understanding.md','packet/private/primary-understanding.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'late_reads_false_admissions_truncation_recovery_coarse_omissions_retained':True,'parent_process_lapse':'An initial rg --files AGENTS.md search traversed outside the intended exact inputs and returned unrelated filenames, with output clipping. No returned proof or metadata body was opened through that search; it supplied no mathematical premise. The exact root AGENTS.md was then read directly. No perfect-isolation claim.','artifact_scope':'Exact file hashes, sizes and detached anchors. Current mode preservation checked separately; no sealed-mode or directory claim.','mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
