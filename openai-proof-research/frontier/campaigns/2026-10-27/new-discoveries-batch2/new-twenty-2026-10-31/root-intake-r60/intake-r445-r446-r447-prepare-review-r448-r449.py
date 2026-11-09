import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
den=json.loads((ROOT/'inherited-denials-r446.json').read_text());den['utc']=now
reports=[];author_files={}
for number in [445,446,447]:
 A=P/f'expanded-corpus-r{number}';mname='SHA256-MANIFEST.json' if number==447 else 'MANIFEST.json';m=json.loads((A/mname).read_text())
 rawfiles=m['sha256'] if number==447 else m['files']
 mf={x['path']:x for x in rawfiles} if isinstance(rawfiles,list) else {n:({'sha256':v} if isinstance(v,str) else v) for n,v in rawfiles.items()}
 if number==445:assert len(mf)==150
 if number==447:assert len(mf)==119
 for n,v in mf.items():
  q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==v['sha256'],str(q)
  if 'bytes' in v:assert q.stat().st_size==v['bytes']
 exclusions=m['precisely_named_terminal_noncircular_exclusions' if number==445 else 'terminal_noncircular_exclusions']
 assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
 f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==12 and all(sha(Path(n))==h for n,h in f.items())
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
 rr=json.loads((A/'reservation.json').read_text());gates=json.loads((A/'results.json').read_text());assert len(rr['ids'])==20 and set(rr['ids'])==set(map(int,gates))
 prov=json.loads((A/('originals.json' if number==445 else 'original-provenance.json')).read_text())
 prows=[(str(x['id']),x) for x in prov] if isinstance(prov,list) else list(prov.items());assert set(map(int,(k for k,v in prows)))==set(rr['ids'])
 chunks={};rawparts=[]
 for key,row in prows:
  q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];rawparts.append(raw)
  rawhash=row['raw_line_sha256'] if number==446 else row['raw_sha256'];assert dg(raw)==rawhash and raw.endswith(b'\n') and row['newline']
  if number in [445,446]:assert raw==base64.b64decode(row['raw_line_base64'])
  if number==445:assert raw==(A/f'literals/{key}.jsonl').read_bytes()
  if number==447:assert raw==(A/f'originals/{key}.jsonl').read_bytes()
  obj=json.loads(raw);assert obj['mathdb_id']==int(key)
  token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
  assert dg(token)==row['token_sha256' if number==447 else 'statement_token_sha256']
  if number in [445,446]:assert token==base64.b64decode(row['statement_token_base64'])
  else:assert token.decode()==row['token']
  statement=json.loads(token);assert statement==obj['statement']
  assert dg(statement.encode())==row['decoded_utf8_sha256' if number==445 else 'decoded_statement_sha256']
 if number==446:assert collections.Counter((A/'original20.jsonl').read_bytes().splitlines(keepends=True))==collections.Counter(rawparts)
 receipts=[]
 for q in sorted(A.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 budget=json.loads((A/'search-budget.json').read_text());events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events)
 assert counts==dict(attempt=13,success=7,unavailable=6) if number==445 else counts==dict(attempt=7,success=6,unavailable=1)
 for e in events:
  if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
  if e['event']=='unavailable':
   key=urlsplit(e['url']).hostname.lower()+unquote(urlsplit(e['url']).path).rstrip('/')
   den['blocked_keys']=sorted(set(den['blocked_keys'])|{key})
   den['records'].append(dict(url=e['url'],reason=dict(status=e.get('status'),error=e.get('error'),restriction='Identified artifact unavailable ALL new alternate deliveries; no retry, cache/mirror/API/author/version/DOI workaround. Registry-root scope is the failed root/metadata artifact, not a blanket denial of every distinct proof publication or every GitHub repository.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'),ordinal=e.get('ordinal'))))
 if number==445:
  assert budget['calls_used']==3 and budget['queries_used']==9
  for k in [1,2,3]:json.loads((A/f'search{k}-full-response.json').read_text())
  process='Access failures preserved; no guard/policy/budget violation reported. Native tool/writer telemetry incomplete; no universal compliance claim.'
  summary='351988 full ordinary Gaussian-kernel/determinant/forest-coefficient/Wiener/hitting-time proof PROPOSAL, independent review unpaid. Actual final DAM389(2026)119-125403, Sidorenko1994 primary403; specific EJC21(2014)P4.9 companion unread; no routine exclusion or novelty clearance.350146 optimal pancake integral palette and354432 3-weight total-labeling gaps. Other17 primary bodies unread. No formal dispatch.'
  allgates={k:{a:b for a,b in v.items() if a not in ['literal']} for k,v in gates.items()}
  author_files={str(A/n):v['sha256'] for n,v in mf.items()};author_files[str(A/mname)]=sha(A/mname)
  for n in exclusions:author_files[str(A/n)]=sha(A/n)
 elif number==446:
  assert budget['calls_precharged']==1 and budget['query_strings_precharged']==3;json.loads((A/'search-response-1.json').read_text())
  process='FAIL retained: live search counters replaced without first reading/authenticating continuity; no actual over-cap inferred. Network stopped on detection, no historical repair. No acceptance eligibility.'
  summary='335867 source-own Theorem3.6 refutation;336931 literal adjacency-spectrum proof is source invariant-definition correction, both zero.343634 polymatroid,331065 occupancy,334518 Kempe routes retain full-scope gaps. Other15 primary bodies unread.'
  allgates=gates
 else:
  assert budget['calls_used']==1 and budget['queries_used']==3;json.loads((A/'search-response-1.json').read_text())
  process='FAIL retained: current registry attempt late after significant investment; HTTP504 preserved. No retry/alternative delivery or mathematical acceptance; exact history reconciliation was timely.'
  summary='347983 conditional eight-side geometric refinement does not prove required six-side bound n>=19;343664 odd-circuit labeling and331752 staircase coupling remain gaps. All0; three selected primary bodies, other17 unread; specified cited proofs/finals/figures/current proof bodies unpaid.'
  allgates=gates
 report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/mname),verified_manifest_files=len(mf),verified_original_bindings=sorted(rr['ids']),verified_frozen_bindings=12,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ORDINARY_PROPOSAL_TO_INDEPENDENT_REVIEW_NO_CREDIT' if number==445 else 'ZERO_QUALIFIED_SURVIVORS_PROCESS_FAIL_RETAINED',scientific_summary=summary,process=process,all20_gates=allgates,root_scope='Documentary integrity/provenance/routing only; root performed no mathematical solving/program/compiler/checker execution',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions,root_reader_notes='Bounded schema readers initially assumed a files map in r447 sha256 manifest and used wrong list accessor; failures occurred before mutations, then explicit schema-specific readers recovered. These are root metadata-reader errors, not mathematical or worker failures.')
 save(P/f'expanded-corpus-r{number}-parent-integration.json',report);reports.append(report)

den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1016/j.dam.2026.03.043','s0166218x26001903','2109.09249','10.1016/0012-365x(94)90388-3','0012365x94903883'})
den['root_tree_hitting351988_scope']='Actual final351988 JiZeng DAM389(2026)119-125 DOI10.1016/j.dam.2026.03.043/PIIS0166218X26001903/source2109.09249 unavailable403: ALLnewbodydeliveries original/versions/arxiv/author/mirror/cache/DOI blocked. Existingv4 explicitly copied only, no final equivalence. Sidorenko1994DM131263-277 DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 also403 ALLalternate delivery denied. Distinct Csikvari-Lin2014EJCP4.9 not automatically denied, cannot indirectly recover either blocked work. Four exactregistryroot artifacts504unavailable; no API/README/tree/root alternate metadata refresh; this is not blanket denial of every independently identified distinct proof publication.'
den['root_r445_r446_r447_scope']='All60 literal/original bindings and three frozen12 verified; all0credit. r445351988 ordinary full proposal goes independent review, no formal dispatch. r446counter-continuityFAIL/no inferred over-cap andr447late-registryFAIL preserved. OpenAIroot504 repeated in independent concurrently assigned lanes before this root union update, not a root-issued retry. All old denial/quarantine scope retained.'
denpath=ROOT/'inherited-denials-r448.json';save(denpath,den)

# A new independent source/mathematics reviewer receives only copied completed evidence.
A=P/'expanded-corpus-r445';L=P/'tree-hom-hitting-source-review-sol-r1';assert not L.exists();L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(A/n,n)
cp(ROOT/'charge_search.py','charge_search.py');cp(denpath,'inherited-denials.json')
for n in ['ACTUALBRIEF.md','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','results.json','originals.json','literals/351988.jsonl','sources/hitting.pdf','sources/hitting.txt','sources/hitting-metadata.html','sources/tree-path.pdf','sources/tree-path.txt','source-read-inventory.json','access-inventory.json','history-inventory.json','prior-exact-matches.json','guard-ledger.jsonl','search-budget.json','search1-plan.json','search2-plan.json','search3-plan.json','search1-full-response.json','search2-full-response.json','search3-full-response.json','MANIFEST.json','frozen-after.json']:
 cp(A/n,'inputs/author/'+n)
cp(P/'expanded-corpus-r445-parent-integration.json','inputs/ROOT-AUTHOR-INTEGRATION.json')
cp(ROOT/'accepted57-review-context.json','inputs/accepted57-scopes.json')
cp(P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json','inputs/prior39-scopes.json')
cp(P/'expanded-corpus-r442/registry-inventory.json','inputs/registry-navigation-r442.json')
save(L/'INPUT-ORIGINS.json',origins)
save(L/'reservation.json',dict(ids=[351988],source_url='https://arxiv.org/abs/2109.09249',role='Independent full ordinary proof/source/prior/significance review, no formal routing',credit=0,accepted_new=57,target_new=60))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n')
save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text());common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Current55/60','Current57/60').replace('prior94total','prior96total').replace('Supplied55','Supplied57').replace('Inherited denial union r432','Inherited denial union r448')
detail='''
Independent review351988. Active/planned expanded-corpus-r448 and expanded-corpus-r449 completely protected even metadata/reservation/stat/read/hash/glob/list/poll. No mathematical programs, enumeration, CAS, solver, Lean/compiler/checker/formalAPI. New source review only; implementation DORMANT.

O1 FULL ORDINARY PROOF: Personally derive or refute EVERY bridge independently, not repeat the author's prose. Exact literal is all equally sized finite unweighted trees T,Tprime with hom(T,G)>=hom(Tprime,G) for EVERY finite simple target G, then source average hitting-time index alpha(Tprime)>=alpha(T). Audit target graph domain, size0/1 conventions, connectedness/positive-degree standing assumptions, all diagonal/random-walk conventions, factor2, ordering directions and equality. No weakening to paths/stars/size-transfer-related pairs or only finite list of target graphs. The proposed mechanism uses bounded Gaussian kernel finite-simple random graphs/injective-map error, continuum Gaussian integral/determinant, Cauchy-Binet forest coefficients and large-c limit, Wiener/hitting-time identity. Check independence for injective maps, noninjective errors, measurability/existence/normalization, principal-minor/rank/root choices and exact highest two coefficients, asymptotic cancellation, finiteness/strong Markov/recurrence. Repair real gaps in full ordinary detail or precise GAP. Standard upstream analytic facts may be cited precisely, but every new deduction paid. No root proof validation is supplied.

O2 SOURCE FIDELITY: Personally read the actual copied full MathDB object/raw token and actual arxiv2109.09249v4 source definitions, question and surrounding theorem/proof/hypotheses, relevant figures and bibliography. Authenticate actual page/label and compare all quantifiers. Author claims n1 convention not literal cleanup; adjudicate source-defined domain explicitly, no endpoint credit. Final DAM389(2026)119-125 DOI10.1016/j.dam.2026.03.043/PIIS0166218X26001903 returned403; ENTIRE work unavailable for ALLnewbodydeliveries including original/versions/arxiv/author/DOI/cache/mirror. ONLYcopiedv4 may be read; do not fetch originalv1/currentrecord/final/metadata or seek alternate source delivery. V4 is NOT final equivalence. Retain precise final-source HOLD, no blind waiver or forced worldwide final absence. No formal dispatch regardless of ordinary outcome.

O3 ACTUAL PRIMARY COMPARISON/SIGNIFICANCE: Named Sidorenko1994DM131263-277 DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 returned403: ALLnew deliveries denied, no alternate preprint/author/mirror/cache/version/DOI/search-for-body recovery. Its functional order/necessary-condition theorem proof specifically unread; retain HOLD if applicability cannot be settled. Copied Csikvari-Lin Homomorphisms of Trees into a Path is independently readable: actual full statements/proofs/last questions/bibliography, not just author summary. Its reference7 Graph homomorphisms between trees, EJC21(2014)P4.9 is a DISTINCT specifically identified accessible-prior question not yet denied; under budget locate actual primary body by observed official links and read actual Wiener-based necessary-order/extremality theorem AND proof. Determine a COMPLETE earlier-result-to-all-pair-target bridge or bounded concrete nonmatch. A source-own size-transfer order/subcase is not the full arbitrary Sidorenko order. No exclusion merely from Gaussian/Laplacian standard tools, shortness or formal burden. Strongest contrary significant-content case required alongside any complete routine bridge. No claim exact earlier printed proof/witness without actual source. No author message, account, library proxy, browser or bypass. If any new access failure entire work unavailable, stop that artifact; no retry/alternate delivery. This is focused new comparison, not repeat the author's three broad searches.

O4 FAMILY/REGISTRY/FORMAL LIMITS: Compare trusted57accepted+39prior full scopes personally, scope only/no certificate re-audit, one possible family max. Four public registry-root artifacts all returned504; no root/README/tree/API/branch/metadata alternate refresh, no retries. Copied earlier r442 root-head inventory is DATED NAVIGATION ONLY, not newly authenticated current heads/body/chronology and not blanket novelty. It is not a blanket denial of every distinct independently identified proof publication, but cannot be used to indirectly rebuild denied root metadata. Any concrete exact proof counterclaim needs its actual independently accessible body; otherwise precise HOLD. Generic worldwideunknown is not automatic veto; bounded nonmatch not worldwide novelty. Current scientific deficiencies remain separate, no formal feasibility self-certification. If ordinary survives, give dependency-ordered DORMANT full-literal Lean obligations and feasibility limits, no implementation/dispatch.

O5 PROCESS/BOOKKEEPING: Read copied original author guard/outcomes/full-search responses and root intake; access failure not misconduct, don't invent no-gap or universal process PASS. Own future SEARCH uses immutable charge_search.py under run.py with a persisted own plan containing top-level queries list of EXACT strings. Helper reads live counters plus previous charge ledger, verifies continuity, rejects duplicates/exhaustion and writes precharge through ownwriter. Do NOT directly replace/edit search-budget.json or charge ledger. After successful precharge run that exact native call ONCE and save FULL actual response immediately before subsequent work. Helper is bookkeeping only, no network client. Focused max2calls6queries/8GET hops total, all routes351988. Preserve charged attempts even native failures; no reset/refund/backfill. The first two shell commands are standalone lines, not punctuation-delimited prose. An inert extra own-verifier argument with exit0/all hashes verified under caps is recorded command-fidelity deviation, not automatically external-source policy breach or abandonment; serious access/frozen/protected/cap/network/budget violations retain stop/disclosure. All copied/helper/frozen inputs unchanged.

Deliver complete REVIEW.md and keyedreview.json with O1-O5 and all gates, full independently checked ordinary proof or exact GAP, primary obligation/source map, complete adaptation/nonmatch and contrary significance case, family comparison, dormant plan if useful, full access/read/figure/search/resource inventories, actual receiptJSON/hash manifest with precise terminal exclusions and standalone frozen-after. No credit/acceptance/formal execution. Root57/60 unchanged.
'''
task='Independent tree-homomorphism/hitting-time source and full ordinary proof review in '+str(L)+'\n'+common.replace('LANE',str(L)).replace('TARGET','351988')+'\nSPECIFIC OBLIGATIONS\n'+detail
(L/'TASK.txt').write_text(task)
bind=dict(author_files)
for q in L.rglob('*'):
 if q.is_file() and q.name!='search-budget.json':bind[str(q)]=sha(q)
save(L/'frozen-inputs.json',bind)
review_ready=dict(utc=now,lane=str(L),task_sha256=sha(L/'TASK.txt'),frozen=len(bind),mathdb_id=351988,model='gpt-6.1-sol',reasoning='high',service='default',credit=0)
save(L/'ROOT-PREP.json',review_ready);save(ROOT/'tree-hom-hitting-review-r1-ready.json',review_ready)
assert all(sha(Path(n))==h for n,h in bind.items()) and not (L/'bootstrap-receipt.json').exists()

# Two disjoint discovery packets while the focused reviewer works.
review_lane=L.name;base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();base_tail=base_source[base_source.index('# Metadata selector:'):];base_tail=base_tail[:base_tail.rfind('\nprint(')]
tree=ast.parse((ROOT/'intake-wavelet-r2-prepare-r444.py').read_text());steering0=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
peer_ids={326555,324571,332073,351988};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406','https://arxiv.org/abs/2109.09249'}
ready=[]
for number,other in [(448,449),(449,448)]:
 L=P/f'expanded-corpus-r{number}';assert not L.exists();active=[review_lane,f'expanded-corpus-r{other}']
 tail=base_tail.replace('selection-routing-r434.json',f'selection-routing-r{number}.json').replace('for num in range(421,434):','for num in range(421,448):')
 tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active))
 tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
 tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60').replace("'frozen_bindings':12","'frozen_bindings':13")
 tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded retained sibling IDs/sourceURLs and reviewer351988/2109.09249 from root metadata without active-body access; accepted57 excluded.')
 tail=tail.replace("shutil.copyfile(denpath,L/'inherited-denials.json')","shutil.copyfile(ROOT/'charge_search.py',L/'charge_search.py')\nshutil.copyfile(denpath,L/'inherited-denials.json')")
 tail=tail.replace("'historical-results-allowlist.json','TASK.txt']","'historical-results-allowlist.json','TASK.txt','charge_search.py']")
 tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2']:")
 tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes').replace('Twelve immutable frozen bindings','Thirteen immutable frozen bindings')\ntask=core+latest")
 steering=steering0.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443',f'ACTIVE {review_lane} and expanded-corpus-r{other}')
 steering+='\nCurrent focusedreview351988 active and entirely protected. Ordinary Gaussian-kernel/determinant/forest/Wiener/hitting-time fullproposal pending independent proof/source/prior/significance/family review; NOformal. Identified finalDAM389(2026)119-125 DOI10.1016/j.dam.2026.03.043/source2109.09249/PIIS0166218X26001903 denied403; Sidorenko1994DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 denied403: ALLnewalternate bodydelivery unavailable. Four exact publicregistryrootartifacts504unavailable; no root/README/tree/API/branch metadataalternate refresh/retry. This does NOTban every distinct proof publication or every GitHubrepo, but cannot indirectly reconstruct denied rootmetadata; cacheddatedheads NAVIGATION ONLY, no newcurrentheads/proofclearance or worldwideabsence. Actual concrete matching proofbody separate obligation if independently identified. All older rootdenialscope includingLiNingJCTB2021redirect-only/CMUthesis202 retained.\n'
 steering+='\nCompletedr442all0:330282/356879publicsource refutations; deBruijn lengthlift/simplematroidrankbound/exactnonabelianEGZ unpaid. r443all0/processFAILlatehistory,345467directsourceexampleendpointperturbation zero;345465/351824sourceownsolved; matching/circumference/unboundedcolorconverse unpaid. r444all0/extra-dot commandfidelity deviation retained with rootdispatchpunctuationambiguity,all20primarybodies/currentregistryunread,zero network. r445350146pancake optimalintegralpalette and354432total3weight gaps,351988reviewonly. r446all0/sourceown335867T3.6refutation/336931spectral-invariant correction,343634/331065/334518 gaps; search-countercontinuityFAILretained,noactualovercapinferred. r447all0/late-registryFAILretained,347983conditional8side notrequired6side,343664odd-circuitlabels/331752staircasesgaps. All completedrootintakes verify hashes/bindings only, not new mathematical clearance.\n'
 steering+='\nNEW BOOKKEEPING: charge_search.py is an additional IMMUTABLE frozen helper; total THIRTEEN bindings. Before EVERY native search, persist a plan with top-level queries list of EXACT querystrings, then invoke ABSOLUTE charge_search.py own-plan-path UNDER run.py. It reads/authenticates live counters and charge ledger BEFORE mutation, rejects alreadycharged plan/exhaustion and writes via ownwriter. No direct budget/charge-ledger replacement or edits. After successful precharge perform that native call EXACTLYONCE, immediately save FULL actual response before other work. Wholelane3calls9queries; no reset/refund/historyrepair, failednativeattempts staycharged. Helper has no network client; GETstillsolefixedguard. Missing currentregistryrootrefresh is an accessHOLD with explicit boundedlimits, not permission to refetch deniedroot or infer worldwideabsence. Before significant investment complete exactID/scalarID AND exact sourceURL structuralhistoryreconciliation; ownsource/publicsolutions checked before claimingnew.\n'
 steering+='\nCOMMAND CLARITY: firsttwocommands exactly standaloneTASKlines,no trailingdot/prosepunctuation. An inert extra own-verifier argument with exit0and all13 hashes verified under caps is a recorded invocation-fidelity deviation, not an external-source policy breach or automatic reason to abandon remaining work. Preserveevidence/correctprospectivecommands; no successfulbootstraprepeat. Genuine protected/frozen/access/cap/network/budget violations retainSTOP/disclosure.\n'
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
 ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{number}','exec'),ns)
 rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
 peer_ids.update(rr['ids']);peer_sources.update(x.get('source_url') for x in rr['rows'])
 fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==13 and all(sha(Path(n))==v for n,v in fb.items()) and not (L/'bootstrap-receipt.json').exists()
 assert 'Current55/60' not in (L/'TASK.txt').read_text() and 'Thirteen immutable frozen bindings' in (L/'TASK.txt').read_text()
 ready.append(dict(lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],role='research',frozen=13))
save(ROOT/'review-r1-r448-r449-ready.json',dict(utc=now,accepted_new=57,target_new=60,intakes=[str(P/f'expanded-corpus-r{n}-parent-integration.json') for n in [445,446,447]],review=review_ready,discovery=ready,latest_denials=str(denpath),model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,intakes=[dict(lane=x['source_lane'],manifest_files=x['verified_manifest_files'],frozen=x['verified_frozen_bindings'],original_bindings=len(x['verified_original_bindings']),receipt_exit_counts=x['receipt_exit_counts']) for x in reports],review=review_ready,discovery=ready)))
