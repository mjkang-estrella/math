"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r498'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r498.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'MANIFEST.json');entries={v['path']:v for v in m['files']};assert len(entries)==len(m['files'])==149
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and raw.decode()==row['raw_line_utf8'] and row['raw_line_path']==f'originals/{key}.jsonl' and (A/row['raw_line_path']).read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['raw_statement_token_utf8'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==obj['statement']==row['decoded_statement_utf8'] and dg(obj['statement'].encode())==row['decoded_statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search{i}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=8)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==840
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
assert read(A/'history-final-access.json')==history
summary='374004 author full printed GL2 equality negation by common nonidentity coset aH retained as missing-coset normalization correction0, not independent qualified PASS.380638 n2 Hall-deficiency packing case/helpers leave all-n capacity-preserving exchange unpaid.380818 cone duality/local interval uncrossing identity leave global cancellation/realization unpaid;380817 distinct not implied by nonnegative cd-index cases.380579 complete author Wagner/disk-transform-to-public Royle-Sokal implication0, public rigorous numerical-root computation attributed not new exact certificate/earlier printed exact amicability refutation.380635 actual Chmutov-Lando mutation theorem/proof still leaves pictured-generator/group-versus-action bridge unpaid.380788 sourceProposition3 equivalent full List Coloring Conjecture, PARK. Thirteen originals unread.149 ownfiles20 corpus bindings13 frozen840 saved historical names verified;8 GET successes3 searches9queries,no new denials; no final-journal equivalence or visual/chord-figure clearance. Initial list-scalar history omission repaired, material truncation recovery and native/transient/writer resource limits retained.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=149,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary verification/routing only; no root mathematical solving/programs/Lean/checkers.')
# Independently completed prime-like Goldbach review: integrity and credit adjudication only.
B=P/'prime-like-goldbach-source-review-sol-r1';bm=read(B/'SHA256-MANIFEST.json');bf=bm['files'];assert len(bf)==107
for n,v in bf.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=B/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
bex=bm['exact_terminal_exclusions'];assert set(bex)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actualb=set()
for q in B.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actualb.add(str(q.relative_to(B)))
assert actualb==set(bf)|set(bex)
brdy=read(ROOT/'prime-like-goldbach-review-r1-ready.json');assert sha(B/'TASK.txt')==brdy['task_sha256']
bfr=read(B/'frozen-inputs.json');assert len(bfr)==34 and all(Path(n).is_relative_to(B) and sha(Path(n))==h for n,h in bfr.items())
for n in ['frozen-before.json','frozen-after.json']:
 v=read(B/n);assert v['count']==34 and v['mismatches']==[]
literal=read(B/'inputs/literal368088.json');assert json.loads((B/'inputs/original368088.raw.jsonl').read_text())==literal and literal['mathdb_id']==368088
brec=[]
for q in sorted(B.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(B) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 brec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert len(brec)==25 and read(B/'terminal_manifest.receipt.json')['exit']==0 and read(B/'scopes_third.receipt.json')['exit']==1
bb=read(B/'search-budget.json');assert bb==dict(calls_used=2,queries_used=6,maximum_calls=2,maximum_queries=6,charged_before_call=True)
bc=[json.loads(s) for s in (B/'search-charges.jsonl').read_text().splitlines()];assert len(bc)==2;prev=dict(bb,calls_used=0,queries_used=0)
for i,c in enumerate(bc,1):
 assert c['sequence']==i and c['before']==prev and sha(B/c['plan'])==c['plan_sha256'] and read(B/c['plan'])['queries']==c['queries'] and len(c['queries'])==3
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+3);assert c['after']==nxt;prev=nxt
 response=read(B/('search-one-full.json' if i==1 else 'search-two-full.json'));assert isinstance(response,(str,dict,list)) and len(json.dumps(response))>1000
assert prev==bb and sha(B/'charge_search.py')==sha(ROOT/'charge_search.py') and not (B/'guard-ledger.jsonl').exists()
family=read(B/'family-comparison.json');assert len(family['rows'])==96
review=read(B/'review.json');v=review['368088'];assert v['ordinary']['gate']==v['literal']['gate']=='PASS' and v['significance']['gate']=='RECOMMEND_EXCLUDE_DOMAIN_CORRECTION' and v['acceptance']['credit']==0 and not v['prior']['public_exclusion']
psummary='368088 independent ordinary/literal/cached-primary PASS retained: injective disjoint prime-residue branches, exact all-integer cutoff preimage bijections/error<=2<3, small/negative cutoffs, Euclidean infinitude and eventual modular exclusion paid before candidate read. Both full2025v1/2023v2 bodies read/material pages visually checked; actual arbitrary-Q scope deliberate, no hidden residue/randomness/primality hypothesis. ROOT EXCLUDE significant-discovery credit as LOCAL-ADMISSIBILITY/DOMAIN CORRECTION, adopting specialist recommendation: prefix-count equivalence leaves fixed residue obstruction wholly unconstrained; construction fails necessary local sum coverage before a corrected global additive problem, no new admissible positive regime/sharp replacement criterion. Strong opposing full universal distribution-only falsification preserved, not shortness-only exclusion. NOT authenticated earlier public refutation or complete routine-prior adaptation; no implicit source admissibility claim. Source metadata onlyv1/no displayed final reference does not prove correction/publication absence; bounded prior/novelty uncleared, no specifically applicable unread proof authenticated. All96 trusted scopes compared with bounded nonoverlap,2023/2025/alternate maps one uncredited family.107 files34 frozen verified,0 GET2 searches6strings,no new denial. Documentary scope KeyError repaired/materialtruncations recovered, native/transient/writer limits retained; no formal dispatch/credit,57/60 unchanged.'
prec=dict(utc=now,source_lane=str(B),task_genesis_verified=True,manifest_sha256=sha(B/'SHA256-MANIFEST.json'),verified_manifest_files=107,verified_frozen_bindings=34,runner_receipts=brec,search_budget=bb,new_get_hops=0,review=review,root_adjudication=dict(disposition='EXCLUDE_SIGNIFICANT_DISCOVERY_CREDIT_LOCAL_ADMISSIBILITY_DOMAIN_CORRECTION',basis='Root adopts completed independent specialist recommendation under campaign substantive-credit rule, preserving genuine deliberate universal-conjecture negation and positive opposing case.',not_claimed=['Earlier exact public refutation','Implicit local-admissibility source hypothesis','Complete routine prior-to-refutation bridge','Shortness-only rejection','Classical Goldbach progress','Formal/campaign acceptance']),scientific_summary=psummary,credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=bex,root_scope='Documentary integrity/credit adjudication/routing only; no root mathematics.')
den=read(ROOT/'inherited-denials-r510.json');den['utc']=now;den['root_r498_scope']=summary;den['root_prime_like368088_review_scope']=psummary;denpath=ROOT/'inherited-denials-r511.json'
# All checks precede integrations and disjoint discovery preparations.
save(P/'expanded-corpus-r498-parent-integration.json',record);save(P/'prime-like-goldbach-source-parent-integration-sol-r1.json',prec);save(denpath,den)
base=read(ROOT/'r499-config.json');base.update(completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{498}),quarantined_discovery_numbers=[395,463,466,482],denials=str(denpath),year_floor=1900,candidate_pool=1000)
base['steering']+='\n'+summary+'\n'+psummary+'\nNo scientific/credit redispatch of368088or aliases; no new source ban inferred from exclusion.\n'
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);readies=[]
for number,peer in [(500,'expanded-corpus-r501'),(501,'expanded-corpus-r500')]:
 config=json.loads(json.dumps(base));config.update(number=number,protected_peers=['expanded-corpus-r499',peer],peer_routing_files=['selection-routing-r499.json']+(['selection-routing-r500.json'] if number==501 else []))
 save(ROOT/f'r{number}-config.json',config);ready=module.prepare(config);al=read(Path(ready['lane'])/'historical-results-allowlist.json')
 for name in al:
  rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
  assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
 readies.append(ready)
assert not set(readies[0]['ids'])&set(readies[1]['ids'])
save(ROOT/'r498-prime-review-completion-boundary-delta.json',dict(utc=now,message=summary+' '+psummary,protected_peers=['expanded-corpus-r499','expanded-corpus-r500','expanded-corpus-r501'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(r498_files=149,r498_frozen=13,r498_bindings=20,review_files=107,review_frozen=34,readies=readies,accepted_new=57,credit=0)))
