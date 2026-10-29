import os,resource,signal,json,hashlib,re,zipfile
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,25));signal.alarm(30)
L=Path(__file__).resolve().parent;A=L/'addon-extracted';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((A/'source-manifest.json').read_text());assert all(sha(A/p)==h for p,h in m.items())
mods=json.loads((A/'modules.json').read_text())
for mod in mods:assert (A/'logs'/(mod+'.log')).read_text()==''
log=(A/'logs/AddonAudit.log').read_text();n=int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]);bs=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',log,re.S);assert len(bs)==n
assert 'Forbidden' not in log
inv=[dict(origin=m,name=nm,type=t,axioms=a,flags=f) for m,nm,t,a,f in bs]
assert all('unsafe=false' in x['flags'] and 'axiom=false' in x['flags'] for x in inv)
rs=[json.loads(s) for s in (A/'runs.jsonl').read_text().splitlines()];assert len(rs)==14 and all(r['rc']==0 and r['kill_reason'] is None for r in rs)
(A/'declaration-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
r={'status':'PASS_SORTED_ADDON_ONLY','fullSourceClaim':False,'credit':0,'fresh_archive_extracted_source_only':True,'modules_rebuilt':mods,'new_origins':['SortedCertificate','FastSmallClosure'],'new_actual_origin_declarations':n,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'partial_generated':[x['name'] for x in inv if 'partial=true' in x['flags']],'archive':json.loads((L/'addon-archive-receipt.json').read_text()),'seconds':sum(x['seconds'] for x in rs),'peak_process_group_rss':max(x['peak_group_rss'] for x in rs),'all_sources_unchanged':True,'closed_bridges':['insertSorted_semantics','edgeFastCheck_implies','successorFastRowCheck_implies','arrayFastClosureCheck_implies'],'kernel_checked_closure_sizes':'1→2→3→4→5 only'}
(A/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');(L/'ADDON-RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
sm=(L/'extracted/logs/SmokeAudit.log').read_text();assert 'AUDIT_TOTAL 1' in sm and 'Forbidden' not in sm
(L/'SMOKE-RECEIPT.json').write_text(json.dumps({'status':'PASS_PAIRWISE_SHARD_IMPORT','declarations':1,'actual_audit':'extracted/logs/SmokeAudit.log','meaning':'Terminal000 and Terminal001 import together; no all-shard family equality claim'},indent=2))
p=L/'SUMMARY.md';s=p.read_text().replace('Work in progress: see FINAL-RECEIPT.json for terminal status, once present.','PASS for components and every supplied terminal row: see FINAL-RECEIPT.json. The main extracted replay checked 147 modules / 10,211 actual-origin declarations in 1191.0 summed run seconds, with sampled peak process-group RSS 2,184,323,072 bytes. All 133 terminal shards passed. The 135,268 source-data rows are an external file length, not a formal animal-family count.')
s+='\n## Completed sorted-list add-on\n\nThe separately archived and freshly extracted `SortedCertificate.lean` and `FastSmallClosure.lean` pass strict replay and actual-origin audit. Lexicographic insertion followed by one translated list equality implies the established semantic checker; sorting is not needed for soundness. Four fast local closures through size five are kernel-checked. See ADDON-RECEIPT.json and source-only-sorted-addon.zip. No claim that full layer eleven is checked follows from this optimization.\n\n`ShardImportSmoke` confirms Terminal000/001 can be imported together; its sole actual declaration is audited separately. No combined all-shard terminal-family equality is asserted. Compiler helpers named `_unsafe_rec` have unsafe=false; the main receipt lists the four generated partial helpers explicitly. All proof and checker safety flags were audited.\n'
p.write_text(s)
p=L/'RESOURCE-NOTES.md';s=p.read_text();s=s[:s.index('SortedCertificate.lean is')]+"SortedCertificate.lean subsequently passed its separate source-only extracted replay and actual-origin audit; see ADDON-RECEIPT.json. It is packaged in source-only-sorted-addon.zip, separately from the unchanged main archive.\n";p.write_text(s)
p=L/'provenance.json';pr=json.loads(p.read_text());pr['status']='COMPONENTS_AND_ALL_SUPPLIED_TERMINAL_ROWS_PASS_NOT_FULL_ENDPOINT';pr['optional_handoffs_read_only']=['root-polyomino-compression-handoff-r1/REVIEW-ADOPTION.json','root-polyomino-potential-integration-r1/ADOPTION.json'];pr['generic_potential_and_geometry_not_duplicated']=True;pr['review_artifacts_external_receipt_corrected']=67;pr['candidate_hashes_external_receipt']=58;p.write_text(json.dumps(pr,indent=2)+'\n')
# A review bundle contains source archives and receipts, never candidate oleans.
files=['source-only-certificate.zip','source-only-sorted-addon.zip','SUMMARY.md','INTERFACES.md','RESOURCE-NOTES.md','provenance.json','FINAL-RECEIPT.json','ADDON-RECEIPT.json','SMOKE-RECEIPT.json','hash-after.json','input-hashes.json','numeric-input.json','source-manifest.json','archive-receipt.json','addon-archive-receipt.json','replay_extracted.sh','replay_addon_extracted.sh','finish_replay.py','finish_addon.py','formal/ShardImportSmoke.lean','formal/SmokeAudit.lean','extracted/declaration-inventory.json','addon-extracted/declaration-inventory.json','extracted/runs.jsonl','addon-extracted/runs.jsonl','runs.jsonl']
files+=['extracted/logs/'+p.name for p in sorted((L/'extracted/logs').glob('*')) if p.name.startswith(('OriginAudit','AuditTerminal','SmokeAudit'))]
files+=['addon-extracted/logs/AddonAudit.log']
manifest={p:sha(L/p) for p in files};(L/'delivery-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');files.append('delivery-manifest.json')
with zipfile.ZipFile(L/'review-bundle.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in files:
  info=zipfile.ZipInfo(f,(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,(L/f).read_bytes())
print(json.dumps(r,indent=2));print('bundle_sha256',sha(L/'review-bundle.zip'))
