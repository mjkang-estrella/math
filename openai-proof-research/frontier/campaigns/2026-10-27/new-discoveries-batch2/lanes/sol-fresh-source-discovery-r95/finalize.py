from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
urls={}
for name in ['fetch-log.json','refresh-log.json','closest-log.json']:
 for x in json.loads((P/name).read_text()):
  if 'file' in x:urls[x['file']]=x['url']
x=json.loads((P/'classical-log.json').read_text());urls['ghomi-spruck.pdf']=x['url']
sources=[]
for p in sorted((P/'sources').iterdir()):
 sources.append({'file':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p),'url':urls.get(p.name),'derived_from':p.name[:-4] if p.name.endswith('.pdf.txt') else None})
guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
obj={'lane':str(P),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED_NO_NOMINATION','discovery_count_credit':0,'campaign_counts':{'additional':8,'total':38},'selected_source':'Hong arXiv2606.01771v4 Question5.5','scope':'Every fixed positive area; all compact convex surfaces in H3, including degenerate bodies with curvature-measure conventions.','ordinary_full_source_result':False,'paid_route_obstruction':'Unequal-cap exact fixed-area variation at c=5/6,z=14/11 has antisymmetric coefficient H<-1/10. Not a source resolution.','strongest_objection':'Ball truncations need not contain global minimizers; both perturbed and unperturbed bodies remain axially symmetric.','precise_gap':'All-convex fixed-area comparison and complete minimizing-shape classification absent.','registry':json.loads((P/'registry.json').read_text()),'registry_hold':'Inherited90commit/300file capped delta and55878path truncated tree not repaired. Two new commits/one file do not fill old gap.','context':json.loads((P/'context.json').read_text()),'duplicate_screen':{'files':json.loads((P/'duplicate-screen.json').read_text())['files'],'hits':len(json.loads((P/'duplicate-screen.json').read_text())['hits']),'scope':'ALL dates, filename-based case-insensitive report/ledger inventory, expanded lexical exact identifiers/authors/families; no final size skip; not semantic clearance.'},'sources':sources,'helper_guard':{'path':str(guard),'sha256':sha(guard),'AS_bytes':512*1024**2,'group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1,'cap_raises':False},'offline_check':'bash run.sh','formal_or_paper_investment':False,'access':'Public HTTP only; no browser/accounts/contact/posts/uploads/git; no403/429/challenge encountered or bypassed.','writes':'Only assigned lane. No shared/candidate/ledger edits.','manifest_policy':'manifest.json excludes itself; provenance.json and all other final lane files included. Finalizer stdout discarded; no post-manifest logs written.'}
(P/'provenance.json').write_text(json.dumps(obj,indent=2)+'\n')
manifest=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name!='manifest.json':manifest.append({'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
for x in manifest:assert sha(P/x['path'])==x['sha256']
assert not (P/'PROOF.md').exists()
print('Finalized and verified',len(manifest),'files;',len(sources),'source artifacts.')
