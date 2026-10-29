import pathlib,json,hashlib,datetime,re,subprocess
b=pathlib.Path(__file__).resolve().parent;proj=b.parents[5];batch=b.parent.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Exact relevant body sections of all-filename returns, bounded in output.
pat=re.compile(r'1905\.01736|Asanjarani|Nazarathy|MMPP|Markov.?modulated.?Poisson|Markovian.?arrival|phase.?type|CoxProcess',re.I)
sections=[]
for ss in (b/'mmpp-duplicate-all.txt').read_text().splitlines():
 p=pathlib.Path(ss)
 if not p.is_file():continue
 t=p.read_text(errors='replace');matches=list(pat.finditer(t));rec={'path':str(p),'sha256':H(p),'matches':len(matches),'sections':[t[max(0,m.start()-220):m.end()+350] for m in matches[:4]]}
 sections.append(rec)
(b/'duplicate-sections.json').write_text(json.dumps(sections,indent=2))
r=subprocess.Popen(['rg','--files',str(proj)],stdout=subprocess.PIPE,text=True)
reports=[]
for line in r.stdout:
 p=line.rstrip('\n')
 if re.search('findings|discovery|summary|provenance',pathlib.Path(p).name,re.I):reports.append(p)
assert r.wait()==0
(b/'all-date-report-filenames.txt').write_text('\n'.join(reports)+'\n')
ctx=[]
for p in [proj/'AGENTS.md',batch/'AGENTS.md',batch/'ledger.json',batch/'prior-campaign-context.json',batch/'NEXT.md',proj/'sources/upstream.json',b.parent/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',b.parent/'sol-fresh-source-discovery-r86/SUMMARY.md',b.parent/'sol-fresh-source-discovery-r86/live-compare-inspection.json',b.parent/'sol-fresh-source-discovery-r88/SUMMARY.md',b.parent/'sol-fresh-source-discovery-r89/fetch.py',b.parent/'sol-fresh-source-discovery-r53/discovery.md',b.parent/'sol-fresh-source-discovery-r84/discovery.md']:
 ctx.append({'path':str(p),'sha256':H(p)})
(b/'context-read.json').write_text(json.dumps(ctx,indent=2))
http=[]
for n in ['http.json','http2.json','http3.json']:http.extend(json.loads((b/n).read_text()))
rec={'finalized_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(b),'credit':0,'counts':{'additional':8,'total':38},'status':'FULL_ORDINARY_CANDIDATE_INDEPENDENT_ELIGIBILITY_HOLD','target':{'authors':['Azam Asanjarani','Yoni Nazarathy'],'doi':'10.1017/S1446181122000013','journal_claim':'Conjecture 3.9','preprint':'1905.01736v1 Conjecture 4.2','witness':{'n':12,'t':'48/5','Q':'unit directed cycle generator','D':'diag(9,8,7,6,5,4,3,4,5,6,7,8)/60','proved_gap_upper_bound':'-1/25000'}},'http':http,'web_search':{'date_utc':'2026-10-29','queries':['"MMPP" "stochastic order" "conjecture" counterexample','"MMPP" "Conjecture 3.9"','"time-stationary" "event-stationary" "counterexample"','"Bounds on the mean and squared" "He" pdf'],'limit':'Search tool did not expose per-query UTC. HTTP retrievals have actual recorded UTC; not a citation-index or worldwide search.'},'access_limits':['One guessed He publisher URL returned500 and was not retried. Author-hosted published PDF returned200.','Withdrawn2018 HTML returned404, abstract200 confirms withdrawal. Pre-withdrawal proof body not obtained.','No403/429/challenge encountered in this lane HTTP attempts; no bypass/proxy/retry loop. Wiley web tool timeout was not retried.','Omega /commits/main resolves an old branch, excluded from current baseline. Default-branch current head read separately.','Registry filenames/deltas are lexical evidence only. No full semantic current registry or worldwide priority clearance.'],'resource_limits':{'address_space_bytes':512*1024*1024,'group_sampled_RSS_bytes':512*1024*1024,'cpu_seconds':210,'wall_seconds':230,'nominal_sampling_seconds':.04,'BLAS_threads':1,'guard_copied_from':str(b.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'guard_sha256':H(b/'helper_guard.py'),'guard_limit_note':'Sampled group RSS/CPU cannot rule out between-sample transients. No cap increase. Largest reported sample in prior.py440774656bytes; exact final checks in check.guard.jsonl.'},'ordinary_proof':'PROOF.md','review_status':'No independent reviewer; two exact methods are same-agent verification.','remaining_gates':['Independent ordinary-math/source/substantive eligibility review','Bounded prior-art and closest literature coverage beyond read bodies','Only after eligibility: authorized formal investment, paper and acceptance workflow'],'finalizer_note':'First report-inventory finalization hit RLIMIT_AS MemoryError while buffering rg --files. Changed to streaming with unchanged caps; no proof check failed.', 'writes':'Assigned lane only. No git/browser/accounts/contacts/uploads/publishing. No Lean or paper.','context_receipt':'context-read.json','registry_receipt':'registry-audit.json'}
rec['artifact_sha256']={str(p.relative_to(b)):H(p) for p in sorted(b.rglob('*')) if p.is_file() and p.name not in ['provenance.json','MANIFEST.sha256']}
(b/'provenance.json').write_text(json.dumps(rec,indent=2))
manifest=''.join(f'{H(p)}  {p.relative_to(b)}\n' for p in sorted(b.rglob('*')) if p.is_file() and p.name!='MANIFEST.sha256')
(b/'MANIFEST.sha256').write_text(manifest)
print(json.dumps({'status':rec['status'],'artifacts':len(rec['artifact_sha256']),'manifest_sha256':H(b/'MANIFEST.sha256'),'duplicate_body_sections':[{'path':x['path'],'matches':x['matches'],'sections':x['sections'][:1]} for x in sections]},indent=2)[:6000])
