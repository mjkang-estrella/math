#!/usr/bin/env python3
"""Read-only exact artifact/input checks; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162t-parent';r=b/'fresh-arithmetic-discovery-r162t';m=r/'packet/private';sha=lambda d:hashlib.sha256(d).hexdigest();load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'850d8fb4a8f7b2ad9d63f945c2c3e44f8d5bc21eb93e623bd3eaa1d2e456e88e','private/MANIFEST.json':'9783d9e33e36a4659cb34efe5a93470d0796342d7d3af608b416516a4b67a0c0','REPORT.md':'a58a0f7bbadb7518e4e3c533bb973e23aaed776d0e42f4c8bfab211073921697'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'verify_packet.py'),'--packet',str(r/'packet'),'--manifest',str(r/'private/MANIFEST.json'),'--final',str(r/'FINAL.md'),'--report',str(r/'REPORT.md'),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['private/MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'private/MANIFEST.json');assert len(manifest['files'])==116 and len(manifest['directories'])==15
raw=(p/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223;lookup={x['path']:x for x in tree['tree']}
selection=load(m/'canonical-tree.json');assert len(selection)==33
for x in selection:assert x==lookup[x['path']]
auth=load(m/'canonical-authentication.json');assert len(auth)==25
for x in auth:
 d=(m/'canonical'/x['path']).read_bytes();y=lookup[x['path']];assert len(d)==x['size']==y['size'] and sha(d)==x['sha256'];assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['size'] for x in auth if not x['path'].endswith('.pdf'))==99732
primary=load(m/'primary/access.json')+load(m/'primary/access-additional.json');assert len(primary)==8
for x in primary:
 rows=[y for y in manifest['files'] if y['path'].startswith('private/primary/') and y['sha256']==x['sha256']];assert len(rows)==1
 d=(r/'packet'/rows[0]['path']).read_bytes();assert len(d)==x.get('size',x.get('bytes')) and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162s-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
for x in load(m/'direct-inputs.json'):
 with (p/x['path']).open('rb') as f:
  if 'interval' in x:f.seek(x['interval'][0]);d=f.read(x['interval'][1]-x['interval'][0])
  else:d=f.read()
 assert len(d)==x['bytes'] and sha(d)==x['sha256']
history=[('frontier/iterations/i36-harmonic-analysis-discovery.md','i36-harmonic-analysis-discovery.txt',[(0,16000),(15900,25600),(27932,36318)]),('frontier/iterations/i37-supergeometric-avoidance.md','i37-supergeometric-avoidance.txt',[(0,14900),(14710,30834),(30834,33143)])]
for original,copy,extents in history:
 for start,end in extents:
  with (p/original).open('rb') as f:f.seek(start);d=f.read(end-start)
  with (m/copy).open('rb') as f:f.seek(start);copied=f.read(end-start)
  assert d==copied
controls=load(m/'integrity-controls.json');assert len(controls)==4 and all((x['returncode']==0)==x['expected_success'] for x in controls)
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()};assert snapshot==load(o/'private/root-before.json') and len(snapshot)==126
v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':116,'payload_bytes':sum(x['bytes'] for x in manifest['files']),'packet_directories':15,'root_files_modes_unchanged':126,'canonical_blobs_against_complete_tree':25,'canonical_selection_entries':33,'reported_complete_canonical_text_blobs':23,'reported_complete_canonical_text_bytes':99732,'primary_acquisition_bindings':8,'primary_payload_files':sum(x['path'].startswith('private/primary/') for x in manifest['files']),'completed_direct_originals_unchanged':4,'direct_input_receipts_checked':8,'selected_original_history_span_comparisons':6,'history_originals':2,'saved_copied_control_cases_match':4,'controls_rerun':False,'finite_diagnostics_saved':load(m/'finite_boundary_checks.json'),'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','verify_packet.py','packet/private/derivation.md','packet/private/source-understanding.md','packet/private/primary-understanding.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'pdf_extraction_failure_and_visual_recovery_late_reads_false_admissions_coarse_omissions_retained':True,'artifact_scope':'Exact packet file/directory membership, payload permission modes/hashes/sizes and three anchors. All current root byte/full-mode preservation separately checked; verifier is read and separately preserved by parent snapshot.','mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
