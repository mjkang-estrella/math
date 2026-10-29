import pathlib,json,hashlib,datetime,re
p=pathlib.Path(__file__).resolve().parent;b=p.parents[1];reg=b/'lanes/root-edge-irregulator-current-prior-r1'
def sha(x):
 h=hashlib.sha256()
 with x.open("rb") as f:
  for block in iter(lambda:f.read(1048576),b""):h.update(block)
 return h.hexdigest()
registry=json.loads((reg/'CURRENT-REGISTRIES.json').read_text())
for which in ['omega','openai']:
 f=reg/(which+'-tree.txt');assert sha(f)==registry[which]['tree_sha256'];assert sum(1 for _ in f.open())==registry[which]['tree_entries']
# Actual matching raw blobs correspond to immutable inventory object ids.
blobs={}
for name,path in [('registry-library.md','Library/notes/connelly2026qfibonomial.md'),('registry-qproduct.md','Blueprint/D5/S0/Certificates/Polynomials/QProductNecessityRefutation.md'),('registry-qproduct.lean','D5/S0/Certificates/Polynomials/QProductNecessityRefutation.lean')]:
 data=(p/'source-evidence'/name).read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 line=next(x for x in (reg/'omega-tree.txt').read_text().splitlines() if x.endswith('\t'+path));assert blob==line.split()[2];blobs[name]={'path':path,'git_blob_sha1':blob}
extras={
'aa9.pdf':'https://math.colgate.edu/~integers/aa9/aa9.pdf',
'original-arxiv.pdf':'https://arxiv.org/pdf/1911.12785v3',
'fourth.pdf':'https://raw.githubusercontent.com/ArtificialZeng/AI-Has-Taste/f3ae144b74f238f22c2b84b5283cb14ce912fd33/pdfs/smallmac_2/SM2-P27_Unimodality_of_the_Fourth_Order_q_Fibonomial_Coefficients.pdf',
'fourth-page.html':'https://github.com/ArtificialZeng/AI-Has-Taste/blob/main/pdfs/smallmac_2/SM2-P27_Unimodality_of_the_Fourth_Order_q_Fibonomial_Coefficients.pdf'}
rows=json.loads((p/'source-evidence/acquisition.json').read_text())
for name,url in extras.items():
 f=p/'source-evidence'/name;rows.append({'name':name,'url':url,'sha256':sha(f),'bytes':f.stat().st_size,'retrieval_utc_approx_from_mtime':datetime.datetime.fromtimestamp(f.stat().st_mtime,datetime.timezone.utc).isoformat(),'time_precision_note':'file write completion time, not independently logged HTTP start'})
old=p.parents[3]/'2026-10-26/new-discoveries/lanes'
# Resolve ancestor explicitly, avoiding any writes to older evidence.
old=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes')
reads=[old/'parent-qfibonomial/FINDINGS.md',old/'parent-qfib-r14/FINDINGS.md',old/'pi-discrete-discovery-r2/FINDINGS.md',old/'parent-qfib-r14/sources/stembridge-carswc.txt',old/'parent-qfib-r14/sources/stembridge-carswc.pdf']
obj={'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; no full ordinary proof; selection reconciliation late','credit':0,'counts_unchanged':{'additional':7,'total':37,'next':38},'primary_sources':rows,'actual_registry_blobs_verified':blobs,'registry_snapshot':registry,'registry_limits':'17:20 dated complete inventories; exact matched bodies read; no full-text global audit, no absence claim, no current-head claim at handback','context_reads':[{'path':str(x),'sha256':sha(x)} for x in reads],'access_limits':['Inherited API403/429; zero API calls/retries','Canonical SIGMA PDF406 not retried; latest arXivv3 actual full body read; no VoR byte equality asserted','Lev DVI web unsupported400; full Han-Ren Proposition3.1 proof read instead','No security challenge encountered/continued','Public fourth-slice chronology beyond observed availability not established'],'resource_caps':{'address_space_bytes':536870912,'sampled_group_rss_bytes':536870912,'cpu_seconds':210,'wall_seconds':230,'sample_seconds':0.04,'blas_threads':1,'runner_reused_from':'sol-fresh-source-discovery-r74/capped_run.py','runner_sha256':sha(p/'capped_run.py')},'failure_record':'failures.md','proof_gap':'Uniform nonnegativity of signed denumerant criterion A for arbitrary positive m,n through floor(D/2).','selection_gate':'FAIL: older first-campaign FINDINGS reconciled after initial selection; corrected and no nomination','web_primary_urls_read':['https://arxiv.org/abs/1911.12785','https://arxiv.org/abs/2605.12822','https://sigma-journal.com/2020/076/','https://math.haifa.ac.il/seva/pub_list.html','https://github.com/ArtificialZeng/AI-Has-Taste'],'files':{str(x.relative_to(p)):{'sha256':sha(x),'bytes':x.stat().st_size} for x in sorted(p.rglob('*')) if x.is_file() and x.name not in ['provenance.json','seal.guard.json']}}
(p/'provenance.json').write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n');print('PASS inventory counts/hashes, actual pinned blob hashes, provenance written')
