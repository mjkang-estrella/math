"""Root-only documentary intake and disjoint metadata packet preparation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent
ROOT=P/'root-intake-r60'
LR=P/'lr-translation-degree-source-proof-review-sol-r1'
D=P/'expanded-corpus-r472'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
def verify(a,mname,exkey,nfiles,nfrozen,nsearch,maxsearch,guardcounts):
 m=json.loads((a/mname).read_text());entries={x['path']:x for x in m['files']}
 assert len(entries)==len(m['files'])==nfiles
 for n,v in entries.items():
  assert not Path(n).is_absolute() and '..' not in Path(n).parts
  q=a/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
 exclusions=m[exkey]
 assert len(exclusions)==3 and mname in exclusions
 assert {str(q.relative_to(a)) for q in a.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
 frozen=json.loads((a/'frozen-inputs.json').read_text())
 assert len(frozen)==nfrozen and all(Path(n).is_relative_to(a) and sha(Path(n))==h for n,h in frozen.items())
 after=json.loads((a/'frozen-after.json').read_text());assert after['count']==nfrozen and after['mismatches']==[]
 receipts=[]
 for q in sorted(a.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(a) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 budget=json.loads((a/'search-budget.json').read_text())
 assert budget['calls_used']==nsearch and budget['queries_used']==3*nsearch and budget['maximum_calls']==maxsearch and budget['maximum_queries']==3*maxsearch
 charges=[json.loads(s) for s in (a/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==nsearch
 prev=dict(calls_used=0,queries_used=0,maximum_calls=maxsearch,maximum_queries=3*maxsearch,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==prev and sha(a/c['plan'])==c['plan_sha256'] and json.loads((a/c['plan']).read_text())['queries']==c['queries']
  nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert prev==budget and sha(a/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[json.loads(s) for s in (a/'guard-ledger.jsonl').read_text().splitlines()]
 counts=collections.Counter(e['event'] for e in events);assert counts==guardcounts
 for e in events:
  if e['event']=='success':assert sha(a/e['destination'])==e['sha256'] and (a/e['destination']).stat().st_size==e['bytes']
 return dict(manifest_sha256=sha(a/mname),verified_manifest_files=nfiles,verified_frozen_bindings=nfrozen,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),search_budget=budget,guard_events=dict(counts),terminal_self_exclusions=exclusions),events
lr,levents=verify(LR,'SHA256-MANIFEST.json','terminal_exclusions',115,21,2,2,dict(attempt=6,success=5,redirect=1))
lrready=json.loads((ROOT/'lr-degree-review-r1-ready.json').read_text());assert sha(LR/'TASK.txt')==lrready['task_sha256']
li=json.loads((LR/'search-inventory.json').read_text())
for n in li['full_responses']:assert json.loads((LR/n).read_text())
assert not json.loads((LR/'access-inventory.json').read_text())['protected_external_read_observed']
lg=json.loads((LR/'keyedreview.json').read_text());assert set(lg)=={'318479'} and lg['318479']['acceptance']['credit']==0
lr.update(utc=now,mathdb_id=318479,source_lane=str(LR),task_genesis_verified=True,review_sha256=sha(LR/'REVIEW.md'),proof_sha256=sha(LR/'PROOF.md'),keyed_review=lg,
 root_disposition='PARK_SPECIFIC_FINAL_SOURCE_AND_SIGNIFICANCE_ADJUDICATION',
 ordinary='Investigator personally completed full ordinary translated-LR degree-preservation proof, including explicit tableau lattice bijection, bounded thickening for arbitrary supporting faces, rational-grid dimension/degree identification, positive offset injection, all-integer eventual polynomiality and degree-zero/Fulton clause. Root records the supplied proof, not a root mathematical validation; newly authored completion has not had a separate independent final proof review.',
 prior='Actual Sherman1603.05626v1 Theorem1.1 and Corollary9.4 concern dimension-two ordinary scaling to n+1, a bounded nonmatch to arbitrary translated degree. Actual Rassart math0308101v2 chamber polynomiality proof and KTW math0107011v2 Fulton section read as existing dependencies. No authenticated matching translated-degree prior theorem identified. Search absence and unavailable registry heads do not establish novelty.',
 significance='Full intended all-face claim goes beyond source dominance subclass. Reviewer documents strongest modest-general-convex-adaptation objection and complete bridge but does not demonstrate an already-established primary growth theorem subsuming the new argument. Root does not infer routine exclusion from shortness or tools. Scientific adjudication remains held; no qualification/acceptance from ordinary completion.',
 source='Cached0904.4778v3 Conjecture5.5 matched. Current arXiv metadata identified JCTA118(2011)1829-1842 DOI10.1016/j.jcta.2011.02.005; actual final request followed one302 to2678-byte redirect-only HTML. Specific final/correction comparison remains unpaid, entire work ALL NEW deliveries unavailable. Guard success retained; explicit cached v3 not final equivalence.',
 process='Documentary image-return serialization failed at524288 characters; original render evidence retained and smaller-page displays recovered. No guard/access/counter breach observed. Exact resource samples, native/transient limits and no universal compliance claim retained. No historical/protected path follow.',
 root_scope='Documentary verification and routing only, no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False)
dd,devents=verify(D,'MANIFEST.json','terminal_noncircular_exclusions',134,13,2,3,dict(attempt=6,success=6))
route=json.loads((ROOT/'selection-routing-r472.json').read_text());assert sha(D/'TASK.txt')==route['task_sha256'] and sha(D/'reservation.json')==route['reservation_sha256']
gates=json.loads((D/'results.json').read_text());bindings=json.loads((D/'literal-bindings.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids']
assert len(ids)==20 and set(ids)==set(map(int,gates))=={row['id'] for row in bindings}
chunks={};sources={}
for row in bindings:
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  raw=q.read_bytes();chunks[str(q)]=(dg(raw),raw.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert raw.endswith(b'\n') and row['newline'] is True and dg(raw)==row['raw_sha256'] and (D/'literals'/f"{row['id']}.jsonl").read_bytes()==raw
 obj=json.loads(raw);assert obj['mathdb_id']==row['id'] and list(obj)==row['keys'];sources[str(row['id'])]=obj['source_url']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==row['decoded_statement']==obj['statement'] and dg(obj['statement'].encode())==row['decoded_sha256']
for i in [1,2]:assert json.loads((D/f'search-response-{i}.json').read_text())
history=json.loads((D/'history-access.json').read_text());assert len(history)==776
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history)
dd.update(utc=now,source_lane=str(D),task_reservation_genesis_verified=True,verified_original_bindings=sorted(ids),source_url_by_id=sources,all20_gates=gates,
 root_disposition='ZERO_QUALIFIED_SURVIVORS',
 scientific_summary='318635 exact-length noncrossing pairing maximum lacks arbitrary cyclic rearrangement/rotation-surjectivity and split-recurrence comparison.368797 all-r ordinarization monotonicity lacks genus-raising closure repair/Hall injection; eventual fixed-r quasipolynomiality and public r1/r2 do not pay full claim.318342 composite/mixed-group zero-sum residue avoidance lacks exact weighted-residue extraction; source prime-modulus theorem only public subcase.318862 actual Le0908.2642v2 source Theorem2 proves target with relative density/monicity/dimension bridge.320203 actual Zhao0909.3354v1 Cor3 provides public regular-independent-set bound; Kahn input attributed.338770 actual DeVos-MoharTh1.7 public finiteness theorem covers usual polygonal tessellations; internal dependencies attributed, not fully audited.319246 empty-hypergraph correction0. No new complete ordinary survivor.',
 reading_limits='Four assigned originals read in material passages, sixteen originals unread; two public followups separately read. No exhaustive final/correction clearance or visual figure audit. Exact source gate limits retained.',
 process='776 saved historical-access paths checked by name only, no external path follow by root. Late explicit denial root-tail recovery after six GETs retained as sequence/output-recovery qualification; no flawless pre-network visibility claim. Six distinct actual PDF payloads, no new unavailable work. Native/transient resource limits retained.',
 root_scope='Documentary provenance/integrity/routing only, no independent root mathematics.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False)
# All verification above precedes integration mutations.
save(P/'lr-translation-degree-source-parent-integration-sol-r1.json',lr)
save(P/'expanded-corpus-r472-parent-integration.json',dd)
den=json.loads((ROOT/'inherited-denials-r475.json').read_text());den['utc']=now
unavailable=json.loads((LR/'scientific-unavailability.json').read_text())
urls=['https://doi.org/10.1016/j.jcta.2011.02.005','https://linkinghub.elsevier.com/retrieve/pii/S0097316511000458']
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(u).hostname.lower()+unquote(urlsplit(u).path).rstrip('/') for u in urls})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1016/j.jcta.2011.02.005','s0097316511000458','0904.4778','generalised stretched littlewood-richardson coefficients'})
den['records'].append(dict(url=urls[0],reason=dict(status=unavailable['transport'],artifact=unavailable['work'],restriction=unavailable['restriction']),evidence=dict(path=str(LR/'scientific-unavailability.json'),sha256=sha(LR/'scientific-unavailability.json'),guard_sha256=sha(LR/'guard-ledger.jsonl'),payload_sha256=sha(LR/'sources/target-final.payload'))))
delta='Completed318479 independent investigator now supplies full ordinary translated-LR degree-preservation argument including explicit tableau model, all supporting faces, rational-grid growth, polynomiality and degree-zero clause. Newly authored proof not yet separate independent final-reviewed; scientific PARK exact final source and significance, no formal dispatch/credit. Actual Sherman1603.05626v1Cor9.4 dimension2ordinaryscaling is a bounded nonmatch, NOT arbitrary translated degree. Rassart actual chamber proof and KTW Fulton section dependencies read; no integral-hive assumption or unread growth theorem import. NEW entire-work delivery restriction: Gutschwager Generalised stretched LR coefficients JCTA118(2011)1829-1842 DOI10.1016/j.jcta.2011.02.005,PIIS0097316511000458,source0904.4778 returned2678-byte Redirecting HTML200 after302; not journal body. ALL NEW hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata UNAVAILABLE,no retry/indirect recovery. Explicit pre-denial frozenv3 only,notfinal equivalence. Guard transport history unchanged. Distinct Sherman,Rassart,KTW primary works NOT denied by this different-work failure.115ownfiles21frozen6GET hops5transport success(3PDF+metadata+redirectHTML),2search6queries; documentary image serialization recovery retained.57/60unchanged.'
den['root_lr318479_scope']=delta
r472scope='Completedr472 zero qualified survivors.318635 lacks exact-length cyclic reordering/rotation bridge;368797 all-r rank-preserving genus injection unpaid;318342 composite/mixed-group exact-residue avoidance unpaid.318862actualLe0908.2642v2Theorem2sourcepublic0;320203actualZhao0909.3354v1Cor3public0;338770actualDeVosMoharTh1.7usualtessellationpublic0 with attributed internal inputs.319246empty-hypergraph correction0. Fouroriginalsread,sixteenunread,two distinctpublicfollowups.134ownfiles20raw/token/decodedbindings13frozen6PDFGETsuccess2search6queries verified.776savedhistorypaths no protected components; late denial-tail recovery qualification retained,no universalprocedurePASS. No newdenials/dispatch/credit.'
den['root_r472_scope']=r472scope
denpath=ROOT/'inherited-denials-r476.json';save(denpath,den)
base=json.loads((ROOT/'r473-config.json').read_text())
steer=base['steering']+'\n'+delta+'\n'+r472scope+'\n'
completed=sorted(set(base['completed_discovery_numbers'])|{472})
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ready=[]
for number,other,peer_files in [(474,475,['selection-routing-r473.json']),(475,474,['selection-routing-r473.json','selection-routing-r474.json'])]:
 config=dict(base);config.update(number=number,protected_peers=['expanded-corpus-r473',f'expanded-corpus-r{other}'],peer_routing_files=peer_files,completed_discovery_numbers=completed,denials=str(denpath),steering=steer,year_floor=2000,candidate_pool=400)
 config['excluded_ids']=sorted(set(config['excluded_ids'])|{318479,322479})
 config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/0904.4778','https://arxiv.org/abs/1111.0531','https://arxiv.org/abs/2212.05733'})
 save(ROOT/f'r{number}-config.json',config)
 rd=module.prepare(config)
 allow=json.loads((Path(rd['lane'])/'historical-results-allowlist.json').read_text())
 assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
 assert all(not any(f'expanded-corpus-r{n}' in name for n in [395,463,466]) for name in allow)
 ready.append(rd)
assert not set(ready[0]['ids'])&set(ready[1]['ids'])
save(ROOT/'lr-r472-completion-boundary-delta.json',dict(utc=now,message=delta+'\n'+r472scope,protected_peers=['expanded-corpus-r474','expanded-corpus-r475'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(accepted_new=57,lr=dict(files=115,frozen=21,exits=lr['receipt_exit_counts'],disposition=lr['root_disposition']),r472=dict(files=134,frozen=13,exits=dd['receipt_exit_counts']),ready=ready)))
