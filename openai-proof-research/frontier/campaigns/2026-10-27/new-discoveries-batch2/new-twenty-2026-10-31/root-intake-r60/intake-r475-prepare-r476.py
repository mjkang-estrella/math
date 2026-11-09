"""Root documentary verification and disjoint discovery routing only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r475'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
route=json.loads((ROOT/'selection-routing-r475.json').read_text());assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=json.loads((A/'manifest.json').read_text());entries=m['files'];assert len(entries)==148
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_noncircular_self_exclusions'];assert set(exclusions)=={'manifest.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
prov=json.loads((A/'literal-provenance.json').read_text());gates=json.loads((A/'results.json').read_text());ids=json.loads((A/'reservation.json').read_text())['ids'];assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['one_based_line']-1];obj=json.loads(raw)
 assert obj['mathdb_id']==int(key) and row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement']==row['statement'] and dg(obj['statement'].encode())==row['statement_sha256']
 assert gates[key]['mathdb_id']==int(key) and gates[key]['literal_gate']['statement_sha256']==row['statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6 and budget['maximum_calls']==3 and budget['maximum_queries']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
 assert json.loads((A/f'search{i}-response.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=7)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
history=json.loads((A/'history-access.json').read_text());assert len(history['read'])==782
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history['read'] for part in Path(x['path']).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history['read'])
summary='317174author no-internal-zeros HALF proved by alternating trails incl loops/multiedges; full logconcavity lacks reversible/injective pair balancing,not a full candidate/helpercredit.321939actualMatomaki2013 rank2proof/reductions read but all-rank mp-1/subset-basis endpoint unpaid; projection does not preserve validity. Actual2610.19965zero-mod-n/nonzero-mod-n2 theorem is a bounded nonmatch,not arbitrary validmultiset result.379122actualSym(k)Tucker primepower/naturaljoin cases public; arbitrary composite invariant subdivisions lack equivariant zero/selection theorem and cycliczero-free map doesnotpaySym(k).331740actualAHK1511.02888v2 Section9 characteristiccoeff logconcavity/unimodality public0,Hodge machinery attributed.322306actualAbe1110.0303v2 intendediff public, literaldrops epsilon(j,i),source-definitioncorrection0.320833finite-x/all-zfinite-support contradiction literalonly,originalunread,wordingcorrection0.'
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=148,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,task_reservation_genesis_verified=True,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Both live before/after counter states,exact plan digests/query strings,immutable helper and full saved JSON responses verified.',root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary=summary,all20_gates=gates,
 reading_limits='Five assigned original works read in stated passages,fifteen originals unread,two distinct comparisons read. No image figure audit or journal/final/correction equivalence claim. No worldwide/currentregistry clearance.',
 process='782 exact saved historical paths checked by name,no protected external pathfollow by root. Two source-scope hits kept separate from arbitrary-rank/BrownColbourn targets. Unsolicited denied-survey/search registry excerpts not used or followed as proof/recovery seeds. Seven actual PDFGETsuccess,no new denials,all runner exits retained,native/transient/writer telemetry unknown,no universalcomplianceclaim.',
 root_scope='Documentary provenance/integrity and routing only,no independent root mathematics/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r475-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r478.json').read_text());den['utc']=now;den['root_r475_scope']=summary+' Root verified148ownfiles20raw/token/decodedbindings13frozen782savedhistorypaths,7GETsuccess2search6queries. Zero qualified survivors,no newdenials/dispatch/credit;57/60unchanged.'
denpath=ROOT/'inherited-denials-r479.json';save(denpath,den)
base=json.loads((ROOT/'r475-config.json').read_text());config=dict(base)
config.update(number=476,protected_peers=['adaptive-lp-path-source-review-sol-r1','qtransversal-directsum-source-review-sol-r1'],peer_routing_files=['selection-routing-adaptive-lp-review-r1.json','selection-routing-qtransversal-review-r1.json'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{473,474,475}),denials=str(denpath),year_floor=2000,candidate_pool=400)
config['steering']=base['steering']+'\nLATEST completedr473: no full-literal survivor;376636author path/blockprobability route independent adaptiveLP review ACTIVE,randomensemble/source/significance unpaid. Barmak On Quillens theorem A for posets thmafinal.pdf404 wholeworkALLnewdelivery unavailable.316630Haaseexactpublic0;316557ArdilaPostnikovexactpublic0.\nLATEST completedr474:373611fullauthorarbitrarypresentationqtransversaldirectsum proof independentreview ACTIVE;actualSaaltinkrankbridge routine-adaptation issue andcontrarysourceexplicitconjecture,notqualified/dispatch.378317pinnedSidorenkopublicapplication0;382541ArmstrongHillarpublic0;382537indexcorrection0. Pemantle Towards a theory of negative dependence negcor.pdf403 wholeworkALLnewdeliveryunavailable;distinctmath0404099notdenied.\nLATEST completedr475: '+den['root_r475_scope']+'\n'
save(ROOT/'r476-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text())
assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466]) for x in allow)
save(ROOT/'r475-completion-boundary-delta.json',dict(utc=now,message=den['root_r475_scope'],new_protected_peer='expanded-corpus-r476',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=148,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],ready=ready)))
