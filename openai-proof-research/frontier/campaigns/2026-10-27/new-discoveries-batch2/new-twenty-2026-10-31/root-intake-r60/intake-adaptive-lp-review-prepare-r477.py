"""Root documentary verification and scientific routing, no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'adaptive-lp-path-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
ready0=json.loads((ROOT/'adaptive-lp-review-r1-ready.json').read_text());assert sha(A/'TASK.txt')==ready0['task_sha256']
m=json.loads((A/'MANIFEST.json').read_text());entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==m['file_count']==137
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_exclusions'];assert set(exclusions)=={'MANIFEST.json','final_manifest.receipt.json','final_manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==22 and all(Path(n).is_relative_to(A) and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==22 and after['mismatches']==[]
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'final_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget==dict(calls_used=2,queries_used=6,maximum_calls=2,maximum_queries=6,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert isinstance(json.loads((A/f'search{i}-response.json').read_text()),str)
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=5,success=4,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failed=next(e for e in events if e['event']=='unavailable');assert failed['status']==403 and failed['url']=='https://escholarship.org/content/qt0zw766c2/qt0zw766c2.pdf'
keyed=json.loads((A/'keyedreview.json').read_text());assert set(keyed)=={'376636'} and keyed['376636']['credit']==0 and keyed['376636']['disposition']=='SCIENTIFIC_PARK'
record=dict(utc=now,mathdb_id=376636,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),review_sha256=sha(A/'REVIEW.md'),proof_sha256=sha(A/'PROOF.md'),gap_sha256=sha(A/'GAP.md'),verified_manifest_files=137,verified_frozen_bindings=22,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,
 root_disposition='PARK_SPECIFIC_INTENDED_ENSEMBLE_AND_SUBSTANTIVE_SCOPE',
 ordinary='Independent path proof PASS under actual one-sided bounds/all violated original cuts,LPcoercivity/uniqueness and globalfactorization. FixedL amplification paid. Reviewer additionally supplies new complete uniformfullrank fixeddegree forest ensemble atn3b,m2b,rate1/3 with iterationcount divergence inprobability,sameensemblebeforealpha; exact weakcomposition bijection/secondmoments/conditionalGaussian events close authors incomplete configuration sketch. This new auxiliary argument has not had a separate external independent review. Root records submitted mathematics,does not solve or execute math.',
 source='Historicalcs0703123v1Conjecture1 genuine constantiterations but ensemble/probability law unspecified. Actualcs0601099v1precursor also constantalpha,notalpha*n. Actual final2008 DOI10.1109/TIT.2008.2006384 reviewed: numbered conjecture omitted,p5402 empiricalaverages/requestforanalysis;different boxcheck/notedconjecture not an authenticated refutation ofthishistorical claim. Final2011 DOI10.1109/TIT.2011.2161920ALP/MALPTheorem2/AppendixA provesboxpreservation/nupperbound,notmatchinglowerbound. These final comparisons now PAID,notunreadsourceHOLDs. No claim omissionestablishes priorrefutation/withdrawalreason.',
 scientific_gap='Uniformprescribeddegree/fullrank ensemble is natural,but arbitrarydegree distributions doesnot explicitly quantify over everymatrix law. Constructed law has disconnected degree1 repetition components; no connected/minimumdegree>=2 intendedensemble result. RootPARK is genuine source-to-ensemble/significance gap and potential omitted-domain repair,not generic worldwideunknown or shortness-based routineexclusion. No specific matching unread prior lowerbound identified,no complete classicalroutinebridge,no authenticated newfull-literal endpoint.',
 prior='Actual2006/2008/2011 primary comparisons read; unavailableTaghavi2008dissertation searchtheorem3.6notproof or matchingcounterexample claim. Boundednonmatches do notclearworldwidenovelty/currentregistries. Distinct retrievedpapers notdeniedbythesisfailure.',
 family='Trusted57+39 boundedscopes compared,no sameALPconvergence endpoint;allpath/block/rate/forest/probabilityhelper refinementsONEfamily,nohelpercredit.',
 process='Ownfrozen/products/explicitPDFskillonly,nohistory/protected/root/authorlane followreported. Exactfirstcommands,completecountercontinuity,failed403retained/noalternate. Large denial/source/family displays recovered before requests,visualpagesinspected. Native/transient/writer/supervisor telemetryunknown,no universalcomplianceclaim.',
 root_scope='Documentary verification and routing only,no root mathematical solving/programs/Lean/checkers.',keyed_review=keyed,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'adaptive-lp-path-source-parent-integration-sol-r1.json',record)
den=json.loads((ROOT/'inherited-denials-r479.json').read_text());den['utc']=now;url=failed['url']
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(url).hostname.lower()+unquote(urlsplit(url).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'0zw766c2','113173907','decoding linear codes via optimization and graph-based techniques'})
den['records'].append(dict(url=url,reason=dict(status=403,artifact='Taghavi2008dissertation Decoding Linear Codes via Optimization and Graph-Based Techniques,eScholarship0zw766c2,academia113173907',restriction='ENTIRE identified dissertation ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retry,alternate identity correction or indirect recovery. Distinct actually acquired2006conference/2008journal/2011efficientimplementation works notdeniedbythisdifferentworkfailure.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
delta='Completed376636independentreview SCIENTIFICPARK: actualone-bound/allcuts pathandGaussianblockproofPASS; newlycompleted uniformfullrank prescribeddegree n3b,m2b fixedrate1/3forestensemble hasTdiverginginprobability forallfixedalpha,sameensemble,exactweakcomposition/secondmomentbridgespaid. Newlyauthoredauxiliaryproofnotseparatefinalreview. Intendedrandommatrix law/admissibility ofdisconnecteddegree1ensemble/substantivescope remainUNPAID; no connected/minimumdegree>=2 result. Actual2008final DOI10.1109/TIT.2008.2006384 READ,numberedconstantiterationconjectureomitted,notanauthenticatedpriorrefutation. Actual2011 DOI10.1109/TIT.2011.2161920Theorem2AppendixAread nupperbound/box/MALPnotlowerbound. DoNOTretainunreadfinalclaim. No matchingpriorlowerbound orcompleteroutineexclusion,no genericnoveltyveto. RootPARKsourceensemble/domainrepair,notformaldispatch/credit. NEWTaghavi2008dissertation Decoding Linear Codes via Optimization and Graph-Based Techniques eScholarship0zw766c2/academia113173907 HTTP403 ENTIREworkALLNEWhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata UNAVAILABLE,noalternate/retry/indirectrecovery. Distinct2006/2008/2011papersnotdenied.137ownfiles22frozen5GET4transport(3PDF+metadata)1HTTP403,2search6queriesverified;57/60unchanged.'
den['root_adaptive_lp376636_scope']=delta;denpath=ROOT/'inherited-denials-r480.json';save(denpath,den)
config=json.loads((ROOT/'r476-config.json').read_text());config.update(number=477,protected_peers=['expanded-corpus-r476','qtransversal-directsum-source-review-sol-r1'],peer_routing_files=['selection-routing-r476.json','selection-routing-qtransversal-review-r1.json'],denials=str(denpath),steering=config['steering']+'\n'+delta+'\n',year_floor=2000,candidate_pool=400)
config['excluded_ids']=sorted(set(config['excluded_ids'])|{376636});config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/cs/0703123','https://arxiv.org/abs/cs/0601099'})
save(ROOT/'r477-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466]) for x in allow)
save(ROOT/'adaptive-lp-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r477',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=137,frozen_bindings=22,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready)))
