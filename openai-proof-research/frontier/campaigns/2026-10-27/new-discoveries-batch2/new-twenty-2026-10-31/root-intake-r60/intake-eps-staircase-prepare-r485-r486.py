"""Root-only documentary integrity, disposition and disjoint routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,collections,datetime,importlib.util,urllib.parse
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def save(p,d):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'ledger.json')['accepted_new']==57
def verify(name,target,nfiles,nfrozen,readyfile,keyedfile,counts,nsearch,nqueries):
 a=P/name;ready=read(ROOT/readyfile);assert sha(a/'TASK.txt')==ready['task_sha256']
 m=read(a/'SHA256-MANIFEST.json');files=m['files'];assert isinstance(files,dict) and len(files)==nfiles
 for n,v in files.items():
  assert not Path(n).is_absolute() and '..' not in Path(n).parts
  q=a/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
 ex=m.get('terminal_exclusions',m.get('precise_terminal_noncircular_exclusions'))
 assert set(ex)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
 actual=set()
 for q in a.rglob('*'):
  assert not q.is_symlink(),str(q)
  if q.is_file():actual.add(str(q.relative_to(a)))
 assert actual==set(files)|set(ex)
 frozen=read(a/'frozen-inputs.json');assert len(frozen)==nfrozen
 for n,h in frozen.items():assert Path(n).is_relative_to(a) and sha(Path(n))==h,n
 after=read(a/'frozen-after.json');before=read(a/'frozen-before.json')
 assert after['count']==before['count']==nfrozen and after['mismatches']==before['mismatches']==[]
 reservation=read(a/'reservation.json');assert reservation['ids']==[target]
 raw=read(a/f'inputs/original{target}.raw.jsonl');literal=read(a/f'inputs/literal{target}.json')
 assert raw==literal and literal==reservation['rows'][0] and literal['mathdb_id']==target
 receipts=[]
 for q in sorted(a.glob('*.receipt.json')):
  v=read(q)
  assert v['cwd']==str(a) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  assert len(v['affinity'])<=2 and v['group_rss_guard_bytes']==6*1024**3 and v['killed'] is None
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 assert read(a/'terminal_manifest.receipt.json')['exit']==0
 budget=read(a/'search-budget.json');assert budget==dict(calls_used=nsearch,queries_used=nqueries,maximum_calls=2,maximum_queries=6,charged_before_call=True)
 charges=[json.loads(s) for s in (a/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==nsearch
 previous=dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['before']==previous and c['sequence']==i and sha(a/c['plan'])==c['plan_sha256']
  assert read(a/c['plan'])['queries']==c['queries']
  assert c['after']==dict(previous,calls_used=i,queries_used=previous['queries_used']+len(c['queries']))
  previous=c['after'];response=read(a/f'search-response-{i}.json');assert isinstance(response,str) and len(response)>1000
 assert previous==budget and sha(a/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[];previous='0'*64
 for i,line in enumerate((a/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
  e=json.loads(line);assert e['seq']==i and e['previous']==previous
  previous=hashlib.sha256(line).hexdigest();events.append(e)
  if e['event']=='success':assert sha(a/e['destination'])==e['sha256'] and (a/e['destination']).stat().st_size==e['bytes']
 assert dict(collections.Counter(e['event'] for e in events))==counts
 attempts=[e for e in events if e['event']=='attempt'];assert len({e['url_key'] for e in attempts})==len(attempts)
 # Guard pins canonical sorted-key JSON, not the plan file's serialization.
 plans={hashlib.sha256(json.dumps(read(q),sort_keys=True).encode()).hexdigest():read(q) for q in a.glob('get-*.json')}
 for e in attempts:
  assert e['routes']==[str(target)] and e['plan_sha256'] in plans
  assert '/server/api/' not in e['url'] and urllib.parse.urlsplit(e['url']).scheme=='https'
 gates=read(a/keyedfile);assert set(gates)=={str(target)} and gates[str(target)]['accepted_credit']==0 and not gates[str(target)]['qualified_survivor']
 return dict(utc=now,mathdb_id=target,source_lane=str(a),task_genesis_verified=True,manifest_sha256=sha(a/'SHA256-MANIFEST.json'),review_sha256=sha(a/'REVIEW.md'),proof_sha256=sha(a/'PROOF.md'),verified_manifest_files=nfiles,verified_frozen_bindings=nfrozen,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=counts,search_budget=budget,keyed_review=gates,terminal_self_exclusions=ex,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,root_scope='Documentary verification/disposition/routing only; no root mathematical solving, programs,Lean or checkers.')
eps=verify('eps-zero-weight-source-review-sol-r1',321798,135,23,'eps-review-r1-ready.json','review.json',dict(attempt=5,success=4,redirect=1),2,4)
stair=verify('poset-polyantimatroid-staircase-source-review-sol-r1',317443,110,26,'staircase-review-r1-ready.json','keyedreview.json',dict(attempt=2,success=1,redirect=1,unavailable=1),1,3)
E=Path(eps['source_lane']);S=Path(stair['source_lane'])
assert read(S/'get_prior_pdf.receipt.json')['exit']==1
assert "PolicyError: Already attempted URL" in (S/'get_prior_pdf.output.txt').read_text()
assert read(E/'get_final_source.receipt.json')['exit']==0
assert (E/'sources/arrays-final-delivery.html').stat().st_size==2699
assert b'Redirecting' in (E/'sources/arrays-final-delivery.html').read_bytes()
eps.update(root_disposition='EXCLUDE_COMPLETE_ROUTINE_RATIONAL_EHRHART_ADAPTATION',ordinary='Independent full quasipolynomial proof PASS, all positive tensor sizes and d>=0. Reviewer repaired author apex gap by a common-interior-point rational boundary triangulation; paid ambient lattice, small-degree polynomial and all admissible-residue exact-degree bridges. No periodN or single-polynomial-onN-multiples claim.',source='Cached1106.5068v1 Conj47 family-of-polynomials interpretation bounded by sourceTheorem31 two distinct constituents. Root personally read exact cachedTheorem31/Conj47 as documentary comparison; source-defined examples already rule out the periodN strengthening. FinalLAA DOI10.1016/j.laa.2012.01.037/PIIS002437951200119X returned2699byte RedirectingHTML, no finalbody equivalence/correction clearance.',prior='ActualLinke1006.5612v2 Theorem1.1 and affine-lattice top-coefficient clause read by root as documentary comparison; reviewer readTheorem1.2 proof and supplies complete EPS-to-rational-polytope model,lattice,dimension,d=0,residue,exact-degree application. Ehrhart/McMullen classical inputs attributed,not original-proof audits. McAllisterWoods2005 period discussion distinct body read,not exactEPS prior.',significance='Root adopts complete routine-adaptation zero-credit recommendation; not shortness,not a claimed earlier printed exactEPS solution. Strongest explicit source-conjecture contrary case retained. Literal source wording/final-source uncertainty does not turn quasipolynomial application into a significant new theorem. No formalization.',process='FivechargedGEThops/fourtransport200payloads(twoPDF,metadataHTML,redirectHTML),two searches/fourqueries. Full responses and actual receipts verified; truncated root documentary display recovered in targeted reads. No claimed universal resource or access certification. All inherited blocks remain; no registryroot reconstruction.',family='Trusted57+39bounded statement-scope nonmatch; all EPSparameter/rank/period/helper variants onefamily. TranslatedLR318479 is PARK and not used as a theorem.')
stair.update(root_disposition='SCIENTIFIC_PARK_GUARD_STOP_RETAINED_NO_DISPATCH',ordinary='Independent reviewer reports full literal/cachedv1 PASS including multiset augmentation, ideal-coordinate bijection, properdimension3, obstruction to every regular cuboid sequence; this is retained reviewed ordinary evidence,not root mathematical validation or formal certificate.',source='Literal geometric equality scope including coordinate permutations/translations reviewed; abstract arbitrary isomorphic re-embedding is not claimed resolved. Cached0806.2096v1 source/fivepage visual review only; denied2009finalchapter remains unread,not equivalent.',prior='Actual2014 Poly-antimatroid polyhedra AMC7(2014)73-82 theorem/proof unread after automatic redirect loop guard stop; distinct2013 Geometry of poset antimatroids actual body also unread. Concrete relevant holds retained,not worldwidenovelty veto or assumed routine bridge.',significance='PARK. No complete applicable primary-to-staircase refutation/classification bridge established. Familiar small poset machinery and cdim<=3 alone are not a completed exclusion. No formal dispatch/fresh retrieval of blockedworks.',process='Reviewer STOP/quarantine preserved. Documentary guardchain establishes exactly two distinct permitted HTTPS requests; PDF302 led back to already-attemptedmetadata, reserve rejected BEFORE dispatching third request, unavailable recorded, no subsequent attempt. No actually performed forbidden repeated/API/HTTP fetch established. Root retains pre-stop ordinary evidence as PARK,does not erase failure/reset ledgers/claim universal procedurePASS. This differs from proven protected-read/API breaches r395/r463/r466/r482 and does not remove those quarantines. Final26clean frozen hashes not offered as a cure.',family='Trusted57+39boundednonmatch; allcyclicwitness/coordinate/helper variants onefamily,zero acceptedcredit.')
delta_eps='CompletedEPS321798independentfullquasipolynomialPASS; authorapexgaprepaired withcommon-interior rationaltriangulation andall-residueexactdegree/d0/ambientlatticebridges. SourceTheorem31 alreadyrulesoutperiodN/singlepolynomialonN-multiples. ROOTEXCLUDEcompleteactualLinke1006.5612v2Theorem1.1rationalEhrhart-to-EPSapplication,notshortness/notearlierprintedexactEPSsolution. NEW ENTIRE original1106.5068/finalLAA DOI10.1016/j.laa.2012.01.037/PIIS002437951200119X ALLNEWdeliveriesunavailable after2699byte RedirectingHTML;cachedpredenialv1onlynotfinalequivalence.135files23frozen5chargedGET4payloads2search4queriesverified;noformaldispatch/credit,57/60unchanged.'
delta_stair='Completed317443independentreviewordinary/v1PASS retained; ROOTSCIENTIFICPARK,notqualified/dispatch. Final2009chapterunread/blocked; actual2014Poly-antimatroidpolyhedra AMC7(2014)73-82 theoremproofunread/blocked; distinct2013Geometryofposetantimatroidsbodyunread(notitselfdenied). No completedprimaryroutineexclusion,noarbitraryisomorphicreembeddingclaim. NEW2014identifiedworkdlibURN:NBN:SI:doc-5FQG3FNZ ALLNEWdeliveryunavailable afterPDF302toalreadyattemptedmetadataGUARDREJECTEDBEFOREthirdfetch. Twoattempts/oneHTML/oneblockedredirect/oneunavailablerow;noactualrepeatHTTP/APIrequest,STOP/failedreceipt/quarantinenoticepreserved,noreset/universalPASS. Pre-stopordinaryevidenceretainedPARK,notpromoted;permanentprovenbreachquarantinesr395/r463/r466/r482unchanged.110files26frozen1search3queriesverified;57/60unchanged.'
# Finish every verification before any integration or packet mutation.
den=read(ROOT/'inherited-denials-r489.json');den['utc']=now
def block(urls,artifacts,identity,status,evidence):
 den['blocked_keys']=sorted(set(den['blocked_keys'])|{urllib.parse.unquote(urllib.parse.urlsplit(u).netloc+urllib.parse.urlsplit(u).path) for u in urls})
 den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{a.lower() for a in artifacts})
 den['records'].append(dict(url=urls[0],reason=dict(status=status,artifact=identity,restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retry/identity correction/indirect recovery. Explicit already-supplied pre-failure cached copies only,notfinalequivalence. Not a blanket topic/author/host denial.'),evidence=evidence))
block(['https://doi.org/10.1016/j.laa.2012.01.037','https://linkinghub.elsevier.com/retrieve/pii/S002437951200119X'],['1106.5068','10.1016/j.laa.2012.01.037','S002437951200119X',"Cayley's hyperdeterminant a combinatorial approach via representation theory"],'Bremner Bickis Soltanifar Cayley hyperdeterminant original1106.5068/finalLAA2012','302followedtransport2002699byteRedirectingHTMLnotpaper',dict(path=str(E/'new-unavailability-review.json'),sha256=sha(E/'new-unavailability-review.json'),guard_sha256=sha(E/'guard-ledger.jsonl'),payload_sha256=sha(E/'sources/arrays-final-delivery.html')))
block(['https://www.dlib.si/details/URN:NBN:SI:doc-5FQG3FNZ','https://www.dlib.si/stream/URN:NBN:SI:doc-5FQG3FNZ/8ae7cffe-36c2-4cb2-b460-c633f357c4cf/PDF'],['Poly-antimatroid polyhedra','URN:NBN:SI:doc-5FQG3FNZ'],'KempnerLevit Poly-antimatroid polyhedra AMC7(2014)73-82','PDF302toalreadyattemptedmetadata;guardrejectedbeforethirdrequest',dict(path=str(S/'QUARANTINE.md'),sha256=sha(S/'QUARANTINE.md'),guard_sha256=sha(S/'guard-ledger.jsonl'),receipt_sha256=sha(S/'get_prior_pdf.receipt.json')))
den['root_eps321798_review_scope']=delta_eps;den['root_staircase317443_review_scope']=delta_stair
denpath=ROOT/'inherited-denials-r490.json'
save(P/'eps-zero-weight-source-parent-integration-sol-r1.json',eps)
save(P/'poset-polyantimatroid-staircase-source-parent-integration-sol-r1.json',stair)
save(denpath,den)
base=read(ROOT/'r484-config.json');base['completed_discovery_numbers']=sorted(set(base['completed_discovery_numbers'])|{483,484})
base['excluded_ids']=sorted(set(base['excluded_ids'])|{321798,317443,316244})
base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/1106.5068','https://arxiv.org/abs/0806.2096','https://arxiv.org/abs/0704.0541'})
base['steering']+='\n'+read(ROOT/'r483-completion-boundary-delta.json')['message']+'\n'+read(ROOT/'r484-completion-boundary-delta.json')['message']+'\n'+delta_eps+'\n'+delta_stair+'\n'
base.update(denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
unit='cyclic-unit-fixed-sums-source-review-sol-r1';unitrouting='selection-routing-unit-sums-review-r1.json'
readies=[]
for n,peer in [(485,'expanded-corpus-r486'),(486,'expanded-corpus-r485')]:
 config=json.loads(json.dumps(base));config.update(number=n,protected_peers=[unit,peer],peer_routing_files=[unitrouting]+(['selection-routing-r485.json'] if n==486 else []))
 save(ROOT/f'r{n}-config.json',config);ready=module.prepare(config)
 allow=read(Path(ready['lane'])/'historical-results-allowlist.json')
 forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
 for name in allow:
  rel=Path(name).relative_to(P)
  assert not any(t in part.lower() for part in rel.parts for t in forbidden)
  assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
 readies.append(ready)
assert not set(readies[0]['ids'])&set(readies[1]['ids'])
save(ROOT/'eps-staircase-completion-boundary-delta.json',dict(utc=now,messages=[delta_eps,delta_stair],new_protected_peers=['expanded-corpus-r485','expanded-corpus-r486'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(eps=dict(files=135,frozen=23,receipt_exits=eps['receipt_exit_counts'],disposition=eps['root_disposition']),staircase=dict(files=110,frozen=26,receipt_exits=stair['receipt_exit_counts'],disposition=stair['root_disposition']),ready=readies,accepted_new=57,credit=0)))
