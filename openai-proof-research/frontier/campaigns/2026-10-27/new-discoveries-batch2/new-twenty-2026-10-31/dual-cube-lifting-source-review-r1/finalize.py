import hashlib,re,atexit
def digest(q):return hashlib.sha256(q.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
review={'schema_version':1,'376322':{
 'mathdb_id':376322,'role':'independent adversarial review','recommendation':'HOLD','authorize_pi_recommended':False,
 'accepted':False,'credit':0,'campaign_count':'52/60','lean_run':False,'replay_claim':False,
 'gates':{'ordinary_mathematics_positive_dimension':'PASS','literal_current_author_endpoint':'HOLD','source_graph_semantics':'PASS_WITH_SOURCE_TABLE_CORRECTION','available_versions':'PASS_BOUNDED','latest_journal_corrections':'HOLD_BOUNDED','prior_subsumption':'HOLD_MATERIAL_SOURCE_UNREAD','novelty':'HOLD','significance':'HOLD','formal':'NOT_RUN'},
 'literal_resolution':{'positive_n':'complete proof','n_zero_distinct_set':'premise forces k=1; F1=K2 is connected','n_zero_indexed_repetition_allowed':'fails at k=2; Q0 repeated empty trees satisfy path condition vacuously','source_explicit_positive_n_found':False,'no_silent_hypothesis_change':True},
 'proof':{'path_internal_equivalence':'verified including two-partition argument','internal_connected_dominating':'verified for >=3 vertices','coordinate_matching_obstruction':'verified','compatible_graph_connectivity':'verified by two-step coordinate walks','xor_bit_bridge':'verified against adjacency clauses; printed ID table reversed','gluing_tree':'verified connectivity and bridge acyclicity','edge_and_internal_disjointness':'verified','k1_n1':'verified','full_derivation':'REVIEW.md'},
 'material_missing_passage':{'doi':'10.1109/TPDS.2019.2931904','required':'main k-CIST compound-graph sufficient condition and proof, exact port-map and cluster hypotheses','test_substitution':'G=K_(2^n,2^n), H=Q_n, port y at L_x joined to port x at R_y','http_result':'normal DOI redirect -> IEEE8781860 HTTP202 zero bytes','body_read':False,'full_subsumption_proved':False,'complete_routine_adaptation_proved':False},
 'source_versions':{'2607.25917':['v1 2026-07-28','v2 2026-09-21'],'2608.00900':['v1 2026-08-02 metadata','v2 2026-08-22 body'],'current_v2_matches_frozen':True},
 'registry_heads':{'openai/math':'4eaee87548250b2682affda7d05d947c05554bae','LeanPool/lean-pool':'55b1badf31a1a5eb2f5c11f3334e6bd72a5c6ff2'},
 'limits':['2020 theorem unavailable','no exhaustive registry clearance','raw singleton convention unresolved','no full journal/corrections clearance'],
 'integrity_deviations':['frozen baseline taken after initial candidate read, all169 matched supplied immutable hashes','early bootstrap RSS samples not persisted','one bs4 import failure; no install','one telemetry timer-shadowing failure; repaired','early combined output truncations; decisive passages re-read'],
 'forbidden_actions_performed':False,'children_started':0,'jobs_remaining':0,'review_utc':now}}
(p/'review.json').write_text(json.dumps(review,indent=2)+'\n')
read_records=[]
source_names={'376322.html':'definitions, Theorem1, Theorem2/full proof, Section4.2 criterion, Conjecture1, SVG Figure4; not every appendix','376322-v1.html':'same relevant passages and actual Figure4; not every appendix','dual-companion.html':'complete printed construction/proof discussion, polynomial, extraction, Remark1, references; no verifier execution','376322-abs.html':'version and publication metadata','dual-companion-abs.html':'version and publication metadata'}
for name,depth in source_names.items():
 q=a/'sources'/name;read_records.append(dict(path=str(q),sha256=digest(q),bytes=q.stat().st_size,read_depth=depth))
for key,depth in [('main-v2','explicit v2 bytes compared with frozen; same body'),('main-abs','current version/publication metadata'),('companion-abs','current version/publication metadata'),('openai-head','currentOid only'),('leanpool-head','currentOid only'),('qin2020','empty response, NO THEOREM BODY'),('qin2022','definitions, Theorems1/2, Theorem6 statement and partial partition proof; not all figures or entire paper')]:
 q=p/(key+('.pdf' if key=='qin2022' else '.html'));read_records.append(dict(path=str(q),sha256=digest(q),bytes=q.stat().st_size,read_depth=depth))
(p/'source-read-inventory.json').write_text(json.dumps({'sources':read_records,'inherited_receipts':str(a/'http-receipts.jsonl'),'current_receipts':'http-receipts.jsonl','downloaded_is_not_read':True},indent=2)+'\n')
searches=['"10.1109/TPDS.2019.2931904" pdf','"The existence of completely independent spanning trees for some compound graphs" theorem','"2607.25917" correction journal lifting','"compound graphs" "CISTs" "Qin" "Theorem"','"dual-cube" "lifting" spanning trees 2026','"Constructing Two Completely Independent Spanning Trees in Dual-Cubes" journal correction','"Qin" "compound" "CIST" filetype:pdf','"2931904" site:ntub.edu.tw','"The existence" "compound graphs" pdf -site:researchgate.net -site:scispace.com -site:minicod.com']
(p/'access-search-log.json').write_text(json.dumps({'queries':searches,'managed_tool':'web.run','managed_process_metrics':'service-managed, local affinity/RSS unavailable; not represented as capped local scripts','managed_opens':['DOI -> internal inaccessible error; later one normal direct HTTP request logged','Temple primary2022 PDF','Qin BUCT faculty publication list'], 'body_clearance':{'2020':'none','2022':'partial, see read inventory'},'incidental_denied_host_snippets':'Broad searches surfaced MathDB/Togni indexed snippets; no opens or retries and no clearance inferred','no_retry_hosts':['MathDB','Palomar recent.json','GitHub API','Togni TLS-failed host','Wiley'],'source2020_no_more_attempts_after_empty202':True},indent=2)+'\n')
frozen=json.loads((p/'frozen-inputs.json').read_text());rows=[dict(path=s,expected=h,actual=digest(pathlib.Path(s))) for s,h in frozen.items()]
assert len(rows)==169 and all(r['expected']==r['actual'] for r in rows)
(p/'frozen-after.json').write_text(json.dumps(dict(utc=now,count=len(rows),all_match=True,files=rows),indent=2)+'\n')
inputs={}
def add(q,kind):
 if q.is_file():inputs[str(q)]={'sha256':digest(q),'bytes':q.stat().st_size,'access':kind}
for s in frozen:add(pathlib.Path(s),'frozen hash check; body read only for targeted sources/metadata listed separately')
for name in ['TASK.txt','frozen-inputs.json','historical-results-allowlist.json']:add(p/name,'review input')
for d in [*p.parents,p]:add(d/'AGENTS.md','applicable instructions when present')
allow=json.loads((p/'historical-results-allowlist.json').read_text())
for s in allow:
 if 'crown-vnumber-' in s:continue
 q=pathlib.Path(s)
 if q.is_file() and q.stat().st_size<=2500000:add(q,'exact allowlist historical text screen only')
root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
for name in ['sources/upstream.json','sources/CONTENTS.md']:add(root/name,'pinned metadata / bounded target term screen')
for name in ['ledger.json','prior-campaign-context.json']:add(p.parent.parent/name,'root metadata scalars only; no historical lane expansion')
(p/'input-manifest.json').write_text(json.dumps(inputs,indent=2)+'\n')
(p/'PROCESS.md').write_text('All local commands used timeout Python -I -B and set actual two-CPU affinity plus RLIMIT_CPU/AS before reads. First command used CPU25/wall30/AS2GiB; later CPU120/wall140/AS6GiB. Runner records real per-process usage where available. Bootstrap RSS was not persisted; one timer callback sample was lost, and is not fabricated. First baseline came after initial candidate read, all169 supplied hashes matched. Early outputs included oversized/truncated combined dumps; candidate and decisive passages were re-read. No mathematical enumeration, Lean, solver, numerical search, git, account/browser action, install, child agent or remote mutation. The pdftotext subprocess returned0 and was reaped; HTTP executor threads joined. No background jobs were started. See process-receipts.jsonl and tool execution receipts for exit statuses.\n')
# Close the final measured process receipt before hashing output files.
atexit.unregister(receipt);receipt()
outputs={q.name:{'sha256':digest(q),'bytes':q.stat().st_size} for q in p.iterdir() if q.is_file() and q.name not in ['output-manifest.json','output-manifest.sha256']}
(p/'output-manifest.json').write_text(json.dumps(outputs,indent=2)+'\n')
(p/'output-manifest.sha256').write_text(digest(p/'output-manifest.json')+'  output-manifest.json\n')
print(json.dumps({'review':'HOLD','ordinary':'PASS positive n','frozen_after':len(rows),'all_match':True,'pi_recommended':False,'output_files_hashed':len(outputs),'jobs_remaining':0}))
