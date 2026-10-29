from pathlib import Path
import json,hashlib,datetime,re
P=Path(__file__).resolve().parent
pat=re.compile(r'2410\.13920|Bernoulli structure|Fontana|Semeraro|2312\.01819|Tsallis.{0,70}heat|2111\.06997|varentropy',re.I)
rows=[]
for name in (P/'all-report-target-filenames.txt').read_text().splitlines():
 p=Path(name);h=hashlib.sha256();snips=[];carry='';count=0
 with p.open('rb') as f:
  while True:
   b=f.read(65536)
   if not b:break
   h.update(b);s=carry+b.decode(errors='replace');ms=list(pat.finditer(s));count+=len(ms)
   for m in ms:
    if len(snips)<3:snips.append(s[max(0,m.start()-200):m.end()+500])
   carry=s[-800:]
 rows.append({'path':name,'sha256':h.hexdigest(),'bounded_sections':snips,'chunk_match_count_may_repeat_boundaries':count,'streamed_entire_file':True})
(P/'all-report-bounded-sections.json').write_text(json.dumps(rows,indent=2))
d=json.loads((P/'sources/omega-final-delta').read_text());files=[x['filename'] for x in d.get('files',[])];delta={'commits':d.get('total_commits'),'files_returned':len(files),'paths':files,'target_path_hits':[s for s in files if re.search('fontana|semeraro|bernoulli|varentropy|tsallis',s,re.I)],'limit':'GitHub compare file-list cap300; paths only for new delta, no semantic absence claimed'}
(P/'live-final-delta-summary.json').write_text(json.dumps(delta,indent=2))
prov={'lane':str(P),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'EXCLUDE; no nominated discovery','discovery_count_credit':0,'counts_read':{'additional':8,'total':38},'sources':json.loads((P/'http.json').read_text()),'web_access_not_hashed':[{'url':'https://arxiv.org/html/2410.13920v2','status':'404, mistaken nonexistent version, no retry'},{'url':'https://projecteuclid.org/journals/electronic-communications-in-probability/volume-30/issue-none/The-Bernoulli-structure-of-discrete-distributions/10.1214/25-ECP741.full','status':'iframe wrapper only; no mathematical body read'}],'source_labels_read':{'2410.13920v1':['Theorem2.1','Corollary3.1','Proposition3.1','Corollary3.3','Proposition4.1 and proof','Section4.2'],'2111.06997v1':['Theorem1.1 and introduction'],'2312.01819v4':['Tsallis definition','Conjecture1 Eq11','order2 theorem','Example2'],'2605.11656v1':['Theorem1','Theorem2','Proposition1','explicit mixture Eq2-3']},'exact_gap':'Journal-only future-work question and exact theta-family not body-verified; no certified full source endpoint. Routine source-volume differentiation is explicitly ineligible even if source gap closes.','strongest_objection':'d2 witness and all-d Hessian are routine consequences of published product-simplex volume formula, not substantive new discovery.','falsifiers':['journal theta-family or volume normalization differs from explicitly defined independent-Bernoulli pullback','source product-volume formula differs','error in binomial coefficient derivative identities'],'access_limits':['One institutional PDF403; no retry/bypass/proxy','arXivv2 nonexistent404, v1 history verified','publisher wrapper gave no theorem body','lexical bounded all-date/current registry screens do not certify global absence','new Omega delta paths inspected; new bodies not exhaustively read'],'resources':{'guard':'copied improved helper_guard.py','AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40,'BLAS_threads':1,'caps_raised':False,'sampling_limit':'unsampled RSS transients not excluded'},'scope_exception':'Initial /tmp filename list was moved into lane; no other outside-lane output or shared mutation.','no_children':True,'no_git':True,'no_browser_accounts_contacts_posts_uploads':True,'live_final_delta':delta,'files':[]}
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name!='provenance.json':prov['files'].append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(P/'provenance.json').write_text(json.dumps(prov,indent=2))
print(json.dumps({'reports_streamed':len(rows),'current_delta_commits':delta['commits'],'current_delta_files':len(files),'target_delta_path_hits':delta['target_path_hits'],'provenance_files':len(prov['files']),'credit':0}))
