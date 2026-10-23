#!/usr/bin/env python3
"""Read-only nominee/input authentication; no mathematical review decision."""
from pathlib import Path
import hashlib,json,subprocess
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162w-parent';r=b/'fresh-arithmetic-discovery-r162w';m=r/'packet/private';sha=lambda d:hashlib.sha256(d).hexdigest();load=lambda f:json.loads(f.read_bytes())
a={'FINAL.md':'264b1691ccdd414d29039d9a575b85d7d82e8a7b5a2e0292daccc6e671cb052c','MANIFEST.json':'ba2e0c5165ba4976cba38e54e0f296e3a1bd24d76b58cd3f4afb0ae009c56705','REPORT.md':'7ece3aa51c369d41cd4c56dc99d2b80ce2c24889286699b25a498ef82b840cb9'}
for f,h in a.items():assert sha((r/f).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'packet/notes/verify_packet.py'),'--root',str(r),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True,check=True)
manifest=load(r/'MANIFEST.json');assert len(manifest['files'])==135
raw=(p/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223;lookup={x['path']:x for x in tree['tree']}
selection=load(m/'canonical-tree.json');assert len(selection)==69
for x in selection:assert x==lookup[x['path']]
auth=load(m/'canonical-authentication.json');assert len(auth)==55
for x in auth:
 d=(m/'canonical'/x['path']).read_bytes();y=lookup[x['path']];assert len(d)==x['size']==y['size'] and sha(d)==x['sha256'];assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
primary=[x for x in load(m/'primary/access.json') if 'sha256' in x]+[load(m/'primary/1304.5250v1/access.json'),load(m/'primary/1210.1537v2/access.json')];assert len(primary)==6
for x in primary:
 rows=[z for z in manifest['files'] if '/primary/' in z['path'] and z['sha256']==x['sha256']];assert len(rows)==1
 d=(r/rows[0]['path']).read_bytes();assert len(d)==x.get('size',x.get('bytes')) and sha(d)==x['sha256']
direct=load(b/'discovery-arithmetic-r162v-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
 d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
history=[('i38-inequality-stability-discovery.md',9,26),('i70-symplectic-geometry-discovery.md',7,158),('i74-relative-symplectic-packing.md',9,175)];hs=[]
for name,start,end in history:
 lines=[]
 with (p/'frontier/iterations'/name).open('rb') as f:
  for n,line in enumerate(f,1):
   if n>=start:lines.append(line)
   if n==end:break
 d=b''.join(lines);copied=(m/'history'/name).read_bytes();assert d==copied
 hs.append({'path':'frontier/iterations/'+name,'line_extent_inclusive':[start,end],'bytes':len(d),'sha256':sha(d),'boundary_heading_only_at_last_line':True})
(o/'private/history-originals.json').write_text(json.dumps(hs,indent=2)+'\n')
freeze=load(m/'freeze-receipt.json');assert freeze['sha256']=='fb4e7ccbddfb38a0908622f3c166cce9327d1b91cea0df335ec80b332a4f8bff' and sha((r/freeze['path']).read_bytes())==freeze['sha256']
controls=load(r/'packet/notes/integrity-controls.json');assert [x['exit_code'] for x in controls['results']]==[0,1,1]
snapshot={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()};assert snapshot==load(o/'private/root-before.json') and len(snapshot)==152
proof=m/'author-proof.md';v={'status':'MATCH','anchors':a,'verifier_stdout':run.stdout,'payload_files':135,'payload_bytes':sum(x['bytes'] for x in manifest['files']),'root_files_modes_unchanged':152,'frozen_statement_sha256':freeze['sha256'],'author_proof_sha256':sha(proof.read_bytes()),'author_proof_bytes':proof.stat().st_size,'canonical_blobs_against_complete_tree':55,'canonical_selection_entries':69,'reported_complete_canonical_text_objects':36,'reported_actual_figure_pdfs_visually_read':3,'primary_acquisition_bindings':6,'primary_version_retrieval_failure_disclosed':1,'completed_direct_originals_unchanged':4,'selected_original_history_excerpt_comparisons':3,'saved_copied_control_cases_match':3,'controls_rerun':False,'metadata_is_not_semantic_reading':True,'parent_semantically_read':['REPORT.md','FINAL.md','packet/notes/FROZEN-STATEMENT.md','packet/notes/verify_packet.py','packet/private/author-proof.md','packet/private/prefreeze-feasibility.md','packet/private/source-understanding.md','packet/private/primary-understanding.md','packet/private/author-check.md','packet/private/READING-LIMITS.md'],'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,'late_search_false_admissions_boundary_confirmations_clipped_seam_recovery_retained':True,'source_bearing_author_proof_retained_private_local':True,'artifact_scope':'Exact packet file set, byte sizes/hashes and detached anchors. Parent separately checks all current root full modes/bytes; directory membership/modes are not sealed by this verifier.','mathematical_gate_assigned':False,'accepted':False,'count_change':0};(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
