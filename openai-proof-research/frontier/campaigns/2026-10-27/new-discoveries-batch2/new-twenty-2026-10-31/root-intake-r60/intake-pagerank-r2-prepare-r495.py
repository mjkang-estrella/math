"""Root documentary integrity, denial propagation, disjoint selection. No mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util,re
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'pagerank-uniform-primary-qualification-sol-r2'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
ready=read(ROOT/'pagerank-primary-qualification-r2-ready.json');assert sha(A/'TASK.txt')==ready['task_sha256']
files={}
for line in (A/'MANIFEST.sha256').read_text().splitlines():
 h,n=line.split('  ',1);assert re.fullmatch('[0-9a-f]{64}',h) and n not in files and not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==h,n;files[n]=h
assert len(files)==83
ex=read(A/'MANIFEST-exclusions.json')['exclusions'];assert set(ex)=={'MANIFEST.sha256','manifest_terminal.receipt.json','manifest_terminal.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(files)|set(ex)
fr=read(A/'frozen-inputs.json');assert len(fr)==33
for n,h in fr.items():assert Path(n).is_relative_to(A) and sha(Path(n))==h
for n in ['frozen-before.json','frozen-after.json']:
 v=read(A/n);assert v['count']==33 and v['mismatches']==[]
literal=read(A/'inputs/literal316846.json');assert json.loads((A/'inputs/original316846.raw.jsonl').read_text())==literal and literal['mathdb_id']==316846
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert len(receipts)==17 and read(A/'manifest_terminal.receipt.json')['exit']==0
failure=read(A/'get_csaji.receipt.json');assert failure['exit']==1 and 'Only explicit credential-free HTTPS URLs are allowed' in failure['stderr']
budget=read(A/'search-budget.json');assert budget==dict(calls_used=1,queries_used=2,maximum_calls=2,maximum_queries=6,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1;c=charges[0]
assert c['sequence']==1 and c['before']==dict(budget,calls_used=0,queries_used=0) and c['after']==budget and len(c['queries'])==2
assert sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries'] and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
response=read(A/'search-response-1.json');assert isinstance(response,str) and len(response)==34311
plan=read(A/'get-plan-1.json');assert plan['routes']==['316846'] and plan['destination']=='sources/csaji-alt.pdf' and plan['url']=='https://www.sztaki.hu/~csaji/csaji-pagerank-alt-2010.pdf'
ev=[];previous='0'*64
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==previous;previous=dg(line);ev.append(e)
 if e['event']=='attempt':assert e['plan_sha256']==dg(json.dumps(plan,sort_keys=True).encode()) and e['routes']==['316846'] and e['url'].startswith('https://') and '/server/api/' not in e['url']
counts=collections.Counter(e['event'] for e in ev);assert counts==dict(attempt=2,redirect=2)
assert ev[-1]['location']=='http://old.sztaki.hu/~csaji/csaji-pagerank-alt-2010.pdf' and not (A/'sources/csaji-alt.pdf').exists()
review=read(A/'review.json');assert review['316846']['acceptance']['credit']==0 and not review['316846']['O2']['complete_prior_bridge'] and not review['316846']['O2']['theorem_level_nonmatch']
summary='316846 R2 STOP/HOLD: no new primary theorem body acquired. R1 full ordinary/literal PASS including chain bridge retained, not re-earned; provisional significance conditional on actual prior. Original/final0711.2867 remains403-closed. Csaji ALT2010 institutional URL HTTPS301 to HTTPS302 then HTTP target rejected BEFORE dispatch; logger also failed, only2 actual HTTPS requests and4 ledger rows, no unavailable row fabricated/no HTTP request/retry/HTTPS upgrade. Actual Csaji/Fercoq theorem proofs/action constraints remain unpaid. No public/routine exclusion or theorem-level nonmatch justified.83 own files33 frozen verified,1 charged search2 strings,2 GET hops0 payload. Guard STOP/nonPASS retained, no formal dispatch/credit;57/60 unchanged.'
record=dict(utc=now,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'MANIFEST.sha256'),verified_manifest_files=83,verified_frozen_bindings=33,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,review=review,root_disposition='SCIENTIFIC_PARK_PRIMARY_BODY_AND_FINAL_SOURCE_HOLD',scientific_summary=summary,procedure='Required guard STOP preserved. HTTP redirect rejected pre-dispatch, error logger failed, no manual guard backfill/reset. Native and transient resource peaks unknown; no universal process PASS. Root initial manifest-schema display attempted JSON parse of plain SHA manifest and failed documentary-only; exact plain schema subsequently verified.',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=ex,root_scope='Documentary integrity/routing only; no mathematical solving/programs/Lean/checkers.')
den=read(ROOT/'inherited-denials-r502.json');den['utc']=now;den['root_pagerank316846_r2_scope']=summary
keys={'www.sztaki.hu/~csaji/csaji-pagerank-alt-2010.pdf','sztaki.hun-ren.hu/~csaji/csaji-pagerank-alt-2010.pdf','old.sztaki.hu/~csaji/csaji-pagerank-alt-2010.pdf'}
den['blocked_keys']=sorted(set(den['blocked_keys'])|keys)
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'csaji-pagerank-alt-2010.pdf','pagerank optimization in polynomial time by stochastic shortest path reformulation'})
restriction='ENTIRE identified Csaji-Jungers-Blondel ALT2010 PageRank Optimization in Polynomial Time by Stochastic Shortest Path Reformulation ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable after HTTP redirect guard rejection. No retry/HTTPS-upgrade/alternate identity/indirect recovery. Overlapping Csaji0911.2280/DAM2014 identity must not be used to recover blocked work; relationship not authenticated, not a blanket denial of every distinct PageRank paper. HTTP target was NEVER requested; immutable guard history unchanged despite logger failure.'
den['records'].append(dict(url=plan['url'],reason=dict(status='HTTPS301/HTTPS302 to HTTP target guard rejection before dispatch; failure logger also failed',artifact=plan['source_identity'],restriction=restriction),evidence=dict(path=str(A/'get_csaji.receipt.json'),sha256=sha(A/'get_csaji.receipt.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
delta=summary+' NEW '+restriction
# All checks precede documentary writes or new packet creation.
save(P/'pagerank-uniform-primary-parent-integration-sol-r2.json',record);denpath=ROOT/'inherited-denials-r503.json';save(denpath,den)
base=read(ROOT/'r494-config.json');base.update(number=495,protected_peers=['expanded-corpus-r493','expanded-corpus-r494'],peer_routing_files=['selection-routing-r493.json','selection-routing-r494.json'],denials=str(denpath),quarantined_discovery_numbers=[395,463,466,482],year_floor=2000,candidate_pool=400)
base['steering']+='\n'+delta+'\n';save(ROOT/'r495-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);newready=module.prepare(base)
allow=read(Path(newready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'pagerank-r2-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r495',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=83,frozen=33,receipts=len(receipts),events=dict(counts),budget=budget,ready=newready,credit=0,accepted_new=57)))
