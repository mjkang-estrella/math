from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent
R=next(x for x in P.parents if x.name=='openai-proof-research')
def digest(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
guard=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert digest(guard)==digest(P/'helper_guard.py')
assert not (P/'PROOF.md').exists()
checks=json.loads((P/'check-results.json').read_text());assert checks['status']=='PASS'
sources=[{'path':str(f.relative_to(P)),'bytes':f.stat().st_size,'sha256':digest(f)} for f in sorted((P/'sources').iterdir()) if f.is_file()]
(P/'source-manifest.json').write_text(json.dumps(sources,indent=2)+'\n')
provenance={'lane':'sol-fresh-source-discovery-r107','finalized_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'discovery_credit':0,'counts':{'additional':8,'total':38},'status':'UNRESOLVED main target; routine/public-proof exclusions','claims':[{'source':'https://arxiv.org/html/2507.21316v2','label':'Conjecture9','status':'unresolved','gap':'Actual projective lift/rational realization is not derived from positive K0 inclusion'},{'source':'https://arxiv.org/html/2603.26626v1','label':'ConjectureA','status':'unresolved full scope'},{'source':'https://arxiv.org/html/2603.26626v1','label':'Final unnumbered conjecture after Example4.15','status':'excluded routine source-definition argument'},{'source':'https://arxiv.org/html/2608.22756v1','label':'Conjecture1.1 / Theorem4.10','status':'excluded actual public full proof'}],'duplicate_screen':{'files':5998,'mode':'streaming all-date lexical report-name corpus','semantic_clearance':False},'live_registries':{'omega':'head request403 rate limited; inherited73a5033dd654a16a14fcd1b13277f1a03d81d826','openai':'head request403 rate limited; inherited7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','current_unchanged_claim':False,'aggregate_300_limit_resolved':False},'source_manifest':'source-manifest.json','http_receipts':'http.json','context_hashes':'context-read.json','exact_checks':{'assertions':checks['assertions'],'replay':'sh run.sh','scope':checks['scope']},'resource_guard':{'sha256':digest(guard),'unchanged':True,'address_space_bytes':512*1024*1024,'group_rss_bytes':512*1024*1024,'cpu_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'blas_threads':1},'strongest_objection':'Some suitable rational witness may exist even though an arbitrary positive K0 witness fails; no source counterexample','no_children':True,'no_git':True,'only_lane_writes':True,'no_lean_or_paper':True,'external_mutations':False,'limits':['Complete current registry heads unavailable after single403s','Old inventory/short chains not semantic clearance; aggregate300cap remains','Publisher full journal body403 once','Curtis-Reiner and2026 thesis bodies unread','No worldwide priority claim']}
(P/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
# Exclude self-referential manifest and active finalization log/guard receipt.
files=[f for f in sorted(P.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name not in ['MANIFEST.sha256','finalize.log','finalize.guard.json']]
(P/'MANIFEST.sha256').write_text(''.join(digest(f)+'  '+str(f.relative_to(P))+'\n' for f in files))
print(json.dumps({'payload_files':len(files),'source_files':len(sources),'exact_assertions':checks['assertions'],'guard_identical':True,'credit':0}))
