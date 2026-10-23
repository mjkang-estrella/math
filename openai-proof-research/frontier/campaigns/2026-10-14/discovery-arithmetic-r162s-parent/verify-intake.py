#!/usr/bin/env python3
"""Read-only exact artifact/input authentication, without mathematical gates."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162s-parent';r=b/'fresh-arithmetic-discovery-r162s';m=r/'packet/private';sha=lambda d:hashlib.sha256(d).hexdigest();load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'3d546c8c15c435548bfb78378b597d11dba6812c6cb528b641611a7a2609285b','private/MANIFEST.json':'2b023c28635827005c30ae6e7f84f135de7d10a0610906d9345d205218515c33','REPORT.md':'82af76038120263946767a999303e8bd539a3e1942a681551261de85420b153d'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'verify_packet.py'),'--packet',str(r/'packet'),'--manifest',str(r/'private/MANIFEST.json'),'--final',str(r/'FINAL.md'),'--report',str(r/'REPORT.md'),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['private/MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'private/MANIFEST.json');assert len(manifest['entries'])==47 and len(manifest['directories'])==15
raw=(p/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223;lookup={x['path']:x for x in tree['tree']}
selection=load(m/'canonical-tree.json');assert len(selection)==22
for x in selection:assert x==lookup[x['path']]
auth=load(m/'canonical-authentication.json');assert len(auth)==18
for x in auth:
 d=(p/x['local']).read_bytes();y=lookup[x['path']];assert len(d)==x['size']==y['size'] and sha(d)==x['sha256'];assert x['sha']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
assert sum(x['size'] for x in auth if not x['path'].endswith('.pdf'))==322856
primary=[x for group in load(m/'primary-access.json') for x in group['objects']]
for x in primary:
 d=(p/x['path']).read_bytes();assert len(d)==x['size'] and sha(d)==x['sha256']
for meta,name in [('access.json','paper.pdf'),('wisconsin-access.json','wisconsin.pdf')]:
 x=load(m/'primary/jsw'/meta);d=(m/'primary/jsw'/name).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162r-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
with (p/'sources/CONTENTS.md').open('rb') as f:f.seek(139784);catalogue=f.read(140896-139784)
assert catalogue==(m/'catalogue-exact.txt').read_bytes()
controls=load(r/'controls/results.json');assert controls['own_original_unchanged'] and [x['returncode'] for x in controls['controls']]==[0,1]
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()};assert snapshot==load(o/'private/root-before.json') and len(snapshot)==60
v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':47,'payload_bytes':sum(x['bytes'] for x in manifest['entries']),'packet_directories':15,'root_files_modes_unchanged':60,'canonical_blobs_against_complete_tree':18,'canonical_selection_entries':22,'reported_complete_canonical_text_blobs':17,'reported_complete_canonical_text_bytes':322856,'primary_source_response_and_extracted_object_bindings':len(primary),'additional_jsw_pdf_bindings':2,'completed_direct_originals_unchanged':4,'catalogue_extent_checked':[139784,140896],'saved_copied_control_cases_match':2,'controls_rerun':False,'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','verify_packet.py','packet/private/derivation.md','packet/private/source-understanding.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'initial_full_journal_binary_load_selected_decode_only_disclosed':True,'pdf_extraction_failure_and_recovery_late_reads_false_admissions_coarse_omissions_retained':True,'artifact_scope':'Exact packet file/directory membership, payload hashes/sizes, verifier identity and three anchors. All current root byte/mode preservation separately checked; no sealed-mode claim.','mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
