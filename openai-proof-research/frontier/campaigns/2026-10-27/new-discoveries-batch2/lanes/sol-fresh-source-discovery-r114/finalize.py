import json,hashlib,datetime,sqlite3,re
from pathlib import Path
O=Path(__file__).parent
def digest(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  while b:=f.read(262144):h.update(b)
 return h.hexdigest()
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
db=sqlite3.connect(O/'audit-paths.sqlite')
db.execute('create table if not exists verified_paths(path text primary key)');db.execute('delete from verified_paths')
stats={'records':0,'bytes':0,'duplicate_paths':0,'malformed_records':0,'required_named_files':0,'copied_review_math_files':0,'agent_tools_scripts_openproblem_files':0}
for name in ['audit-manifest.jsonl','audit-manifest-resumed.jsonl']:
 with open(O/name) as f:
  for line in f:
   try:r=json.loads(line)
   except json.JSONDecodeError:stats['malformed_records']+=1;continue
   assert len(r['sha256'])==64
   try:db.execute('insert into verified_paths values(?)',(r['path'],))
   except sqlite3.IntegrityError:stats['duplicate_paths']+=1
   stats['records']+=1;stats['bytes']+=r['bytes'];p=r['path'];low=p.lower()
   if re.search(r'summary|discovery|proof|findings|review|ledger|screened.out',low):stats['required_named_files']+=1
   if 'review' in low and Path(p).suffix in {'.md','.txt','.lean','.tex'}:stats['copied_review_math_files']+=1
   if re.search(r'tools|scripts|agent|openproblem',low):stats['agent_tools_scripts_openproblem_files']+=1
db.commit()
stats['generated_content_echoes_excluded']=json.loads((O/'audit-result-resumed.json').read_text())['excluded_generated']
stats['coverage']='all dates, original listed text/source formats; binaries and environment build dependencies excluded; actual copied-review mathematical files retained'
stats['semantic_result']='Exact source catalogue mention366438 is present in pi-analysis-r1/sources/open-posts.json; different supertoken independence claim374083 also present. No prior same-claim mathematical proof discovered in this bounded audit; not worldwide absence.'
stats['utc']=utc()
(O/'audit-report.json').write_text(json.dumps(stats,indent=2)+'\n')
sources=[]
with open(O/'fetch-receipts.jsonl') as f:
 for line in f:sources.append(json.loads(line))
extra=[('metric-primary.html','https://combinatorialpress.com/um-articles/vol-123/on-some-metric-properties-of-supertoken-graphs/'),('bailey-cameron.pdf','https://maths.qmul.ac.uk/~pjc/preprints/bsod.pdf'),('omega-localgirth-refutation.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/89cda9c274d1122b7676173296af3047c3b64cd1/Problems/elzein-mortada-saturated-packing-conjecture-refutation.md')]
for name,url in extra:
 p=O/'sources'/name;sources.append({'url':url,'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':digest(p),'retention_completed_utc':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),'utc_kind':'filesystem completion timestamp; HTTP request-start time not separately logged'})
provenance={'utc':utc(),'status':'FULL_ORDINARY_REFUTATION_SUBSTANTIVE_AND_FRESHNESS_HOLD','credit':0,'counts_unchanged':{'additional':8,'total':38,'next':39},'source':{'authors':['E. T. Baskoro','C. Dalfo','M. A. Fiol','R. Simanjuntak'],'arxiv':'2412.20558v1','doi':'10.61091/um123-02','label':'Conjecture4.2','printed_page':28,'published_online_utc_date':'2025-06-26','arxiv_v1_utc_date':'2024-12-29','quantifiers':'for all positive integers k and base orders n in the source complete-graph definition, dim(F_k(K_n))=n-1','counterexample':{'k':2,'n':10,'resolving_set_size':8,'source_vertices':55},'scope':'Full refutation of universal equality; no exact replacement classification'},'ordinary_math':'PASS self-contained proof and exact replay','substantive':'HOLD: five-position incidence-code repair of classical Johnson three-position construction may be routine adaptation; no independent adjudication','freshness':'HOLD, no worldwide absence or external clearance','registry':{'supplied_omega_head':'89cda9c274d1122b7676173296af3047c3b64cd1','supplied_omega_head_utc':'2026-10-29T20:10:57Z','OpenAI':'7ef5 unchanged, inherited supplied state','new_registry_evidence':'immutable actual Omega packing-refutation proof body only; no new global head inventory','limits':['inherited HEAD/tree403 unclosed','inherited300-file comparison cap unclosed','targeted web index searches incomplete','MathDB direct byte fetch403; web-tool view read','Mycielski direct byte fetch403; web-tool PDF body read'],'chronology':'2024-12-29 source;2025-06-26 published source;2011 Johnson predecessor;2026-04-07 supertoken successor;our private proof2026-10-29. No priority inference from dates alone.'},'audit':stats,'sources':sources,'guard':{'path':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','unchanged':True,'AS_groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'poll_ms':40,'BLAS_threads':1},'Lean':False,'paper':False,'children':False,'git_or_shared_edits':False,'external_posting':False}
(O/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
with open(O/'manifest.jsonl','w') as f:
 for p in sorted(O.rglob('*')):
  if not p.is_file() or p.name in {'manifest.jsonl','verification.json','finalize-log.txt','finalize-guard.json','verification-guard.json'} or p.suffix=='.sqlite' or p.name.endswith(('.sqlite-journal',)):continue
  f.write(json.dumps({'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':digest(p)})+'\n')
print(json.dumps({'audit':stats,'status':'PACKET_WRITTEN'}))
