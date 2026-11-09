from pathlib import Path
import json,hashlib,datetime,re,resource,subprocess,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent; sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((p/'reservation.json').read_text());raw=json.loads((p/'raw-records.json').read_text());s=p/'sources'
rows={
388067:('park_source_gap','Egres timeout; no complete uniform-subdivision answer.','No primary definition/proof-body review; literal read.','388067.html'),
389512:('park_source_gap','Notes URL 404; net adjacency and Cheeger normalization unpaid.','Literal read; primary body unavailable.','stflour.pdf'),
388053:('park_no_polynomial_algorithm','Draw graph and complementary orientation remain coupled; partial NP-completeness does not settle this problem.','Literal read and Egres search excerpt; page HTTP timeout; no technical-report proof body read.','388053.html'),
389548:('park_infinite_no_route','No nonconstant bounded harmonic function in full generality.','1010.3365 definition, Conjecture 1 and nearby discussion; notes unavailable.','1010.3365'),
388114:('park_source_gap','Finite divisorial Brill–Noether bound not proved.','Literal read, primary timeout; search leads not full proof review.','388114.html'),
388676:('exclude_known_degeneracy_park_intended','Collinear-centre infinite tangents are already printed; intended cubic construction absent.','TOPP full problem page and printed quadratic recipe; Illinois degeneracy note. No AAKS proof-body audit.','388676.html'),
388066:('exclude_complete_source_bridge','Pinned strong thin-tree theorem implies f(epsilon)=max(1,ceil(C/epsilon)).','Actual pinned main theorem/introduction; current catalogue; no full upstream proof audit.','thin-'),
374161:('exclude_exact_published_source_proof','Pan Theorem 1.2 is the full reserved assertion.','v1 definitions, theorem, prime-power induction and main proof body read; external cited base/classification not independently audited.','2604.12553'),
342739:('park_after_three_ordinary_routes','Arbitrary-cover matching inequality/injection is unpaid; double-cover tower and attractive-potential shortcuts fail.','v5 definitions, statements and Sections 2–3 proofs; target passages v1–v5 and EJC Conjecture 16 read.','1905.06678'),
325667:('park_after_three_ordinary_routes','Need fourth-point closure independent of A4, or a fully certified A1–A3 counterexample.','v1 Theorem1.2, Bruck–Bose definitions, Theorem3.2 statement/initial proof, A4 uses and Section5 Lemma5.1 proof; not full manuscript.','1305.6673'),
320030:('park_famous_uniform_no_route','No polynomial bound uniform in facet count and dimension.','v1 Chapter2 Conjecture2.0.3 located; broader proof-body review not done.','1006.2416'),
378642:('park_full_locus_no_route','Minuscule/global criteria do not classify full non-Gorenstein locus.','v2 Conjecture1 and surrounding discussion read; v1 fetched but equivalent target wording not recovered. No journal/citing-body audit.','math_0409490'),
378056:('park_analytic_no_route','No full Galois representation construction.','Final Conjecture9.8 passage read in v1; no general analytic proof-body review.','math_0309478'),
378057:('park_analytic_no_route','No uniform proof of Maass spectral simplicity.','Conjecture9.9 passage read in v1; numerical evidence not proof.','math_0309478'),
388660:('park_classical_enumeration_insufficient','Generic exhaustive enumeration/Burnside is not a substantive new counting answer.','Complete current TOPP page and references read; cited enumeration articles not read.','388660.html'),
373368:('park_full_classification_no_route','Bicontractions are only a known subfamily; signature rank reformulation is not structural classification.','v1 matching-covered/separating definitions, Section4 statement passages, Cor28–29, Prop30 and conclusion; proof reading selective; Figure3 caption/recipe not visual review.','2603.00334'),
374223:('exclude_literal_domain_correction_park_source','Literal Min(Q) is singleton {0}; source asks compactness of minimal prime ideals, which remains unpaid.','v1 ideal/filter/topology definitions, Theorems2.17–2.20/Main Theorem proof and Remark2.21 example/conjecture read; no visual figure review.','2604.15498'),
374619:('park_notation_conflict_and_classification','Source final iota is independent domination; MathDB prose says independent locating-domination. No full characterization either way.','v1/v2 final Conjecture1, v2 parameter definitions, Theorem1 and nearby bounds; not all algorithm/proof sections.','2605.07361'),
375281:('park_uniform_dyadic_no_route','Fano is not dyadic; no valid full counterexample or triangulation construction.','v1 definitions, Theorem2.8 and Section6 Conjecture6.5; no SMT execution or complete proof-body audit.','2606.13960'),
375789:('park_after_three_ordinary_routes','No general connected graph count inequality or finite witness; white-set recurrence unpaid.','v1 Section2.2 correspondence, path/star proofs, partial tree transformation statements, Section5 conjecture and cycle recurrence proof; not full algorithm sections.','2607.03894')}
receipts=[json.loads(f.read_text()) for f in sorted(s.glob('*.receipt.json'))];(p/'receipts.json').write_text(json.dumps(receipts,indent=2))
terms=[str(i) for i in r['ids']]+['horizontal class transposition','translation oval','perfect edge dominat','quasicomplement','soccer','thin.tree','non.Gorenstein','gonality','Eulerian orientation','dyadic','Ramanujan','Cheeger','Cartier','Cassels']
registry={}
for f in ['openai-current-CONTENTS.md','truth.html','pool-projects.yml','pool-index.lean']:
 t=(s/f).read_text(); matches=[]
 for term in terms:
  hit=list(re.finditer(term,t,re.I));
  if hit:matches.append({'term':term,'count':len(hit),'first_contexts':[t[max(0,m.start()-140):m.end()+300] for m in hit[:3]]})
 registry[f]={'sha256':sha((s/f).read_bytes()),'matches':matches,'scope':'Content/name routing only; no exhaustive theorem/code review.'}
for f in ['openai-head.html','truth-head.html','pool-head.html']:
 t=(s/f).read_text();registry[f]={'sha256':sha((s/f).read_bytes()),'current_oids':sorted(set(re.findall(r'currentOid\":\"([0-9a-f]{40})',t)))}
(p/'registry-screen.json').write_text(json.dumps(registry,indent=2))
result={}
for id in r['ids']:
 k=str(id);x=raw[k];rec=x['record'];status,gap,depth,prefix=rows[id];primary=[f for f in s.iterdir() if f.name.startswith(prefix) and not f.name.endswith('receipt.json')]
 result[k]={'mathdb_id':id,'title':rec['title'],'literal_statement':rec['statement'],'full_parsed_record':rec,'provenance':{**{a:v for a,v in x.items() if a!='record'},'raw_file':f'raw/{id}.jsonl','newline_preserved':True,'statement_utf8_sha256':sha(rec['statement'].encode())},'disposition':status,'actual_read_depth':depth,'ordinary_attempts_and_precise_gap':gap,'ordinary_attempts_file':'ORDINARY_ATTEMPTS.md','source_inventory':[{'path':str(f.relative_to(p)),'sha256':sha(f.read_bytes()),'download_is_not_complete_read':True} for f in sorted(primary)],'source_receipts_file':'receipts.json','historical_check':'history-matches.txt; history-source-matches.txt; reconciliation in SUMMARY.md','current_registry_check':'registry-screen.json; exact current public page heads and raw index hashes; no full code clearance','all_primary_versions_journal_corrections_citing_bodies_cleared':False,'source_figures_visually_reviewed':False,'novelty_clearance':False,'full_literal_solution_qualified':False,'pi_execution_qualified':False,'lean_run':False,'independent_review':False,'manuscript':False,'replay':False,'credit_awarded':False}
assert set(result)==set(map(str,r['ids'])) and len(result)==20
(p/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
# History source-family search: read-only, bounded by outer timeout, save actual command.
patterns=sorted(set(v['record']['source_url'].split('/abs/')[-1] for v in raw.values() if '/abs/' in v['record']['source_url']))
cmd=['rg','-n','--max-count','8','--max-columns','1200','--glob','*.md','--glob','*results*.json','--glob','!**/expanded-corpus-r282/**','--glob','!**/corpus/**']
for pat in patterns:cmd+=['-F','-e',pat]
cmd += [str(p.parents[5])]
z=subprocess.run(cmd,capture_output=True,text=True,timeout=90);(p/'history-source-matches.txt').write_text(z.stdout);(p/'history-command.json').write_text(json.dumps({'command':cmd,'returncode':z.returncode,'stderr':z.stderr,'limit':'Prose/results glob and max eight lines per file; not all historical raw/proof files.'},indent=2))
h=sha((p/'reservation.json').read_bytes());assert h==(p/'reservation.sha256').read_text().split()[0]
(p/'reservation-check-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':h,'matches_before':h==json.loads((p/'reservation-check-before.json').read_text())['sha256'],'matches_expected':True,'exact20_keys':True},indent=2))
(p/'resource-log.json').write_text(json.dumps({'fetch_scripts':['fetch_sources.py','fetch_extra.py','fetch_final.py'],'fetch_command':'timeout 140s python -I -B <actual lane script>','caps':'fetch scripts RLIMIT_CPU=120s, AS=6GiB; six I/O workers, no mathematical computation; no affinity cap in fetch scripts; observed CPU activity was short, not independently peak-profiled. Assembly limited to two CPUs, CPU120, AS6GiB.','all_fetch_jobs_completed':True,'no_background_workers_started':True,'rusage_assembly':list(resource.getrusage(resource.RUSAGE_SELF))},indent=2))
print('assembled exact20; reservation',h)
