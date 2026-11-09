import pathlib,json,datetime,hashlib,zipfile
L=pathlib.Path(__file__).parent;B=L.parent
prior=json.loads((L/'prior-routes.json').read_text())
http=[json.loads(x) for x in (L/'http-receipts.jsonl').read_text().splitlines()]
literal=json.loads((L/'literal-bindings.json').read_text())
head={}
for name,n in [('openai','008'),('omega','009')]:
 x=json.loads((L/'downloads'/('request-'+n)/'body').read_text())[0]
 head[name]={'sha':x['sha'],'date':x['commit']['committer']['date'],'scope':'head observation only; earlier bounded screens at previous heads remain explicitly dated'}
c=[]
for i,prefix,status,why,replay in [
 (330264,['coxeter'],'NARROWED','Post-publication author arXiv v3 retains Conjecture1.3; journal identity remains unverified.','WALL_LIMIT'),
 (352038,['continued-fraction','expanded-corpus-r45'],'UNCHANGED','No positive evidence of retained published A.5; retained/changed/removed/resolved status undetermined.','NOT_REQUIRED_KEEP_HOLD'),
 (324342,['conference'],'NARROWED','Actual secondary primary-body description excludes described AG constructions at p=k=19; uninspected row-code remarks/tables remain qualified risk.','RSS_LIMIT')]:
 rows=[r for r in prior if any(r['source'].startswith(p) for p in prefix)]
 binding=next(r for r in literal if r['id']==str(i))
 entry=dict(mathdb_id=i,hold_status=status,recommendation='KEEP HOLD',reason=why,source_gate_policy='qualified reopening supported under TASK precedent, subject to successful capped replay and root ruling' if status=='NARROWED' else 'KEEP HOLD: positive retention evidence missing',prior_routes=rows,prior_routes_text='prior-route-text-excerpts.txt',new_routes_reference='http-receipts.jsonl; search-round2.json; search-round3.json; openalex-web-attempt.json',literal={k:v for k,v in binding.items() if k!='record'},fidelity_new_defect_found=False,replay={'status':replay,'strict_full_replay_pass':False,'fresh_endpoint_axiom_audit_completed':False})
 if i==330264:
  entry['replay'].update(compiled_and_explicit_checker_pass=['GroupSemantics','NormalForm','TraceAction','AutomatonSemantics','WordCounting','MachineInvariant','SpectralDefinitions','ConcreteMachine'],failed_module='SpectralWitness',exit=137,wall_seconds=140,sampled_peak_rss_kib=2816180,log='logs/330264-SpectralWitness.build.log',not_reached=['Endpoint compile','Endpoint checker','fresh #print axioms endpoint'])
  entry['qualified_limits']=['version-of-record body unread','bounded dated citing bodies and registry path screens','Omega current head not body-screened','trusted imported cache','no worldwide priority/minimality claim']
 if i==352038:
  entry['qualified_limits']=['published A.5 status remains material, not qualified away','bounded specialist and citation coverage','r2 relevant-subtree/history screen is not global history clearance','cached MathDB literal is not authenticated current solution state']
 if i==324342:
  entry['replay'].update(failed_module='ConferenceMDS324342',exit=137,wall_seconds=28,sampled_peak_rss_kib=6294620,limit_rss_kib=6291456,log='logs/324342-ConferenceMDS324342.build.log',packet_method='review-owned ZIP of exact r4 unpacked .lean main/audit/control sources followed by safe extraction')
  entry['qualified_limits']=['AG2001 Section2/Props2.1-2.2/tables unread; possible length-n row-code remark not excluded','described constructions only are excluded','GG2008 body unread low risk','incomplete cited/global-registry bodies','Lean conclusion is d<=9, not exact d=9/minimality/classification','trusted imported cache']
 c.append(entry)
out=dict(role='HELD-CANDIDATE REOPENING REVIEW, NOT acceptance',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),priority_order=[330264,352038,324342],credit_awarded=0,acceptance_decision=False,root_decides=True,candidates=c,prior_route_scope='Structured receipts in the named frozen candidate/review/dossier lanes; prose/nonstandard receipts additionally preserved in text inventory and route notes.',new_http_receipts=http,current_registry_heads=head,new_citation_query_result='Two new dated OpenAlex citing query routes inaccessible via web tool; not retried; no fresh citing-body success claimed.',integrity=json.loads((L/'integrity.json').read_text()),ledger_comparison=json.loads((L/'ledger-comparison.json').read_text()),resources=dict(rss_limit_gib=6,cpus=[0,1],cpu_seconds_per_call=120,wall_seconds_per_call=140,MALLOC_ARENA_MAX=2,lean_memory_flag='-M3500',python_isolated=True,one_review_owned_heavy_process_at_a_time=True,background_jobs_remaining=0),conduct=dict(child_agents=0,git_operations=False,browser_tabs=False,shared_writes=False,uploads=False,external_messages=False,credentials=False,TLS_verification_disabled=False,denied_route_retries=False),recommendation_note='NARROWED classifies source/prior-art evidence; KEEP HOLD also accounts for fresh replay failures under the task caps. These failures are not mathematical counterevidence.')
(L/'review.json').write_text(json.dumps(out,indent=2)+'\n')
(L/'search-round1-summary.json').write_text(json.dumps({'queries':['"Ciobanu" "Kolpakov" "Conjecture 1.3" geodesic 2021','"Lachmann" "Wiart" "Conjecture A.5"','"Self-dual codes over" "weighing matrices" pdf Arasu Gulliver'],'raw_response_saved':False,'time':'after initial input reading and before first direct download; exact timestamp not retained','leads':['Gulliver publications.html','Combinatorial Press orthogonal-designs paper','ResearchGate request-only AG entries','DORAS complex-quaternary-paper record'],'use':'discovery only; no body claim from snippets'},indent=2)+'\n')
# Read the non-reopened continued-fraction archive as inert data; never execute its scripts.
with zipfile.ZipFile(B/'expanded-corpus-r45/proof-packet.zip') as z:
 members={x.filename:{'bytes':x.file_size,'sha256':hashlib.sha256(z.read(x)).hexdigest()} for x in z.infolist()}
(L/'continued-fraction-archive-read.json').write_text(json.dumps(members,indent=2))
print('review.json valid;',len(c),'candidates;',len(http),'new direct receipts')
