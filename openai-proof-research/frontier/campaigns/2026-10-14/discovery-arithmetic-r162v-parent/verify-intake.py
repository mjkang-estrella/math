#!/usr/bin/env python3
"""Read-only local packet/input checks. No mathematical gate or publication."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162v-parent';r=b/'fresh-arithmetic-discovery-r162v';m=r/'packet/private';sha=lambda d:hashlib.sha256(d).hexdigest();load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'1eabc5bf6ee88fb58edb5fa664e69b4e472e64936ac61ae98fd317c8aa9980a8','MANIFEST.json':'1c9644c1ddc03107172b51151fdca48fe698ec385c89c5cb96f93de62f3a40e5','REPORT.md':'2da89346524425ce5535f99a9b5b048226b92a3229bbdb6be7d387902be48ec6'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'packet/original/verify.py'),'--root',str(r),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'MANIFEST.json');assert len(manifest['files'])==62 and len(manifest['directories'])==30
raw=(p/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223;lookup={x['path']:x for x in tree['tree']}
selection=load(m/'canonical-selection.json');assert len(selection)==21
for x in selection:assert x==lookup[x['path']]
auth=load(m/'canonical-authentication.json');assert len(auth)==17
for x in auth:
 d=(m/x['local']).read_bytes();y=lookup[x['path']];assert len(d)==x['bytes']==y['size'] and sha(d)==x['sha256'];assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['bytes'] for x in auth if not x['path'].endswith('.pdf'))==352486
primary=load(m/'primary/access.json')+load(m/'primary/late-access.json');assert len(primary)==8
for x in primary:
 rows=[z for z in manifest['files'] if z['path'].startswith('private/primary/') and z['sha256']==x['sha256']];assert len(rows)==1
 d=(r/'packet'/rows[0]['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
receipts=load(m/'direct-receipts.json');assert len(receipts)==9
for x in receipts:
 with (p/x['original']).open('rb') as f:
  if isinstance(x['extent'],list):start,end=x['extent'];f.seek(start);d=f.read(end-start)
  else:assert x['extent']=='complete';d=f.read()
 assert sha(d)==x['sha256']
 if 'bytes' in x:assert len(d)==x['bytes']
direct=load(b/'discovery-arithmetic-r162u-parent/private/next-direct-originals.json');assert len(direct)==5
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
controls=load(r/'packet/original/integrity-controls.json');assert controls['own_original_unchanged'] and len(controls['controls'])==3 and all(x['actual_exit']==x['expected_exit'] for x in controls['controls'])
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()};assert snapshot==load(o/'private/root-before.json') and len(snapshot)==74
v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':62,'payload_bytes':sum(x['bytes'] for x in manifest['files']),'packet_directories':30,'root_files_modes_unchanged':74,'canonical_blobs_against_complete_tree':17,'canonical_selection_entries':21,'reported_complete_canonical_text_blobs':14,'reported_complete_canonical_text_bytes':352486,'reported_actual_figure_pdfs_visually_read':2,'primary_acquisition_bindings':8,'completed_direct_originals_unchanged':5,'direct_original_receipts_checked':9,'saved_copied_control_cases_match':3,'controls_rerun':False,'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','packet/original/verify.py','packet/private/derivation.md','packet/private/source-understanding.md','packet/private/primary-understanding.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'late_primary_reads_clipping_recovery_encoding_correction_coarse_history_omissions_retained':True,'no_eligible_history_mechanism_hits':True,'private_local_child_packet_and_seal_metadata_retained_unstaged':True,'artifact_scope':'Exact packet file/directory sets, lengths/hashes and three anchors. Entire current root byte/full-mode preservation separately checked; no sealed-mode claim.','mathematical_gate_assigned':False,'accepted':False,'count_change':0};(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
