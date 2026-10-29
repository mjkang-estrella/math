import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY));resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
import json,hashlib,datetime,zipfile
from pathlib import Path
R=Path(__file__).parent;F=R.parent/'root-steiner-reflection-final-review-freeze-r1';M=R.parent/'sol-steiner-reflection-manuscript-packet-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
freeze=json.loads((R/'review-freeze.json').read_text());payload=json.loads((R/'extracted/packet-manifest.json').read_text())
for n,v in freeze.items():assert sha(R/n)==sha(F/n)==v['sha256']
for n,h in payload.items():assert sha(R/'extracted'/n)==h
ext=json.loads((R/'artifact-hashes.json').read_text())
for n,h in ext.items():assert sha(M/n)==h['sha256'] and (M/n).stat().st_size==h['bytes'],n
with zipfile.ZipFile(R/'steiner-final-review-packet.zip') as z:
 assert len(z.namelist())==65
 for n,h in payload.items():assert hashlib.sha256(z.read(n)).hexdigest()==h
nested=R/'extracted/evidence/root-steiner-reflection-formal-replay-r1/steiner-source-component.zip'
with zipfile.ZipFile(nested) as z:
 for n in z.namelist():
  if n.startswith('formal/') and n.endswith('.lean'):assert z.read(n)==(R/'own-replay'/n).read_bytes()==(R/'extracted/component'/n).read_bytes()
post={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freeze_verified':freeze,'payload_hashes_verified':len(payload),'archive_entries':65,'external_artifacts_verified':len(ext),'nested_sha256':sha(nested),'six_sources_and_audit_byte_identical':True,'ADOPTION_copy_identical':sha(R/'ADOPTION.json')==sha(F/'ADOPTION.json')}
(R/'hash-after.json').write_text(json.dumps(post,indent=2))
r=json.loads((R/'own-replay/replay-receipt.json').read_text());assert r['declaration_count']==118
for m in r['proof_modules']:assert (R/'own-replay/logs'/f'{m}.log').stat().st_size==0
http=json.loads((R/'http.json').read_text());assert sha(R/'live/target.pdf')=='2475bf1990f404e2bd6bd7e5badf618aaa6dca55199b5648d405aa792c06bab5'
heads=json.loads((R/'heads.json').read_text());heads['unrelated_teorth_request']=heads.pop('count');heads['count']=json.loads((R/'live/count-correct-head.json').read_text())['sha']
files={str(p.relative_to(R)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in R.rglob('*') if p.is_file() and (p.suffix in ['.json','.md','.py','.pdf','.png','.tex','.txt','.log'] or p.name.endswith('.lean')) and not str(p.relative_to(R)).startswith('extracted/') and p.name!='provenance.json'}
pro={'utc':post['utc'],'role':'Independent final reviewer; solo','verdicts':{'source':'PASS arXivv1; publication bounded','mathematics':'PASS','formal':'PASS fresh extracted source-only','novelty':'PASS bounded no-known-resolution only','substantive':'PASS modest depth; root owns judgment','manuscript':'PASS all3pages'},'credit':0,'observed_counts':[5,35],'acceptance_authority':'root','write_scope':str(R.resolve()),'conduct':{'children':False,'git':False,'shared_changes':False,'browser':False,'public_mutations':False},'read_instructions':['ancestor openai-proof-research/AGENTS.md','batch AGENTS.md','ledger.json','prior-campaign-context.json','sources/upstream.json','sources/CONTENTS.md','pdf skill'], 'hash_after':post,'own_formal_receipt':'own-replay/replay-receipt.json','own_packet_receipt':'own-replay/final-packet-receipt.json','actual_row_inspection':'actual-report-inspection.json','own_math':'own-math.json','live_http_receipts':http,'heads':heads,'scope_receipt':'registry-scopes.json','delta_receipt':'delta.json','visually_read':['renders/paper-1.png','renders/paper-2.png','renders/paper-3.png','renders/source-09.png','renders/source-10.png','renders/qi-02.png','renders/qi-03.png'],'search_queries':['"Determinants of Steiner Distance Hypermatrices" Cooper Du','"Steiner" "reflection" "H-eigenvalues"','"Cooper" "Du" "2505.10501"','"Steiner distance" "negative" "H-eigenvalue"','"Cooper" "Du" "C1" "positive definite" Steiner','"Determinants of Steiner Distance Hypermatrices" journal counterexample'],'search_limit':'Search result records in tool transcript; no global novelty or journal-nonpublication guarantee. Primary sources independently fetched/read; secondary snippets not relied on as theorem statements.','resource_limits':{'python_AS_soft_MiB':512,'CPU_seconds':210,'wall_seconds':230,'BLAS_threads':1,'lean_j':1,'lean_M_MiB':2700,'lean_process_group_RSS_ceiling_MiB':2800,'RSS_sample_target_seconds':0.045,'peak_own_sampled_RSS_KiB':max(s['peak_group_rss_kib'] for s in r['steps']),'sampling_limit':'unsampled transients not excluded'},'failures':['Guessed author works.html returned404; actual home later fetched','Initial local source-read command used wrong relative directory; corrected without modifying inputs','Initial Count refresh requested unrelated teorth repo; excluded and corrected','Inherited broad import RSS kill log overwritten before review; observation disclosed, not independently measured here'],'residuals':['root acceptance/count decision','bounded latest/journal and global-priority coverage','elementary ancillary two-orbit substantive objection','upstream and TeX caches reused not rebuilt','symmetrized observation unformalized/uncredited','RSS sampling gaps'],'files':files}
(R/'provenance.json').write_text(json.dumps(pro,indent=2));print(json.dumps({'closure':'PASS','freeze':len(freeze),'payload':len(payload),'external':len(ext),'declarations':118,'maxRSS':pro['resource_limits']['peak_own_sampled_RSS_KiB'],'review_sha256':sha(R/'review.md')},indent=2))
