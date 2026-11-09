import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
A=P/'expanded-corpus-r442';active_peers=['expanded-corpus-r443','expanded-corpus-r444']
m=json.loads((A/'MANIFEST.json').read_text());mf=m['files'];assert isinstance(mf,dict)
for n,v in mf.items():
 q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['precise_terminal_noncircular_self_exclusions'];actual={str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()};assert actual==set(mf)|set(exclusions)
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==12 and all(sha(Path(n))==v for n,v in f.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=set(reservation['ids']);gates=json.loads((A/'results.json').read_text());assert len(ids)==20 and ids==set(map(int,gates))
prov=json.loads((A/'literal-provenance.json').read_text());assert set(map(int,prov))==ids
chunks={};bindings=[]
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line_one_based']-1]
 assert raw==base64.b64decode(row['raw_line_base64']) and dg(raw)==row['raw_line_sha256']
 assert (A/f'literals/{key}.jsonl').read_bytes()==raw
 assert raw.endswith(bytes.fromhex(row['newline'])) and json.loads(raw)['mathdb_id']==int(key)
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token==base64.b64decode(row['raw_statement_token_base64']) and dg(token)==row['raw_statement_token_sha256']
 statement=json.loads(token);assert statement==row['decoded_statement']==json.loads(raw)['statement'] and dg(statement.encode())==row['decoded_utf8_sha256']
 bindings.append(int(key))
rec=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 rec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'manifest_finalize.receipt.json').read_text())['exit']==0
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events)
assert counts==dict(attempt=11,success=11)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_charged']==1 and budget['querystrings_charged']==3
response=A/'search/full-response1.json';assert response.name in {Path(n).name for n in mf};json.loads(response.read_text())
all20={k:{'mathdb_id':v['mathdb_id'],'source_url':v.get('source_url'),'source':v['source'],'ordinary':v['ordinary'],'prior':v['prior'],'acceptance':v['acceptance']} for k,v in gates.items()}
report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=len(mf),verified_original_bindings=sorted(bindings),verified_frozen_bindings=12,runner_receipts=rec,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS',public_source_exclusions=[330282,356879],sustained_gaps={'356624':'Uniform length>=4 obstruction lifting or shortcut-free representation unpaid; positive-m successor does not cover S0; identified2026 shift body unread','342128':'Arbitrary simple matroid fixed-k rank bound or full minimal infinite family unpaid; local density/contraction not sufficient; final EJC body unread','381465':'Arbitrary nonabelian exact E(G)=|G|+d(G) unpaid; m-block reduction is own public Theorem7.2, current coarse upper bound not equality'},coverage='All20 literal reviews; five reserved primary bodies partially read plus two successors; fifteen primary bodies unread. Public356879 theorem exclusion has partial construction/figure audit, no newly certified graph.',all20_gates=all20,procedural_limits='Resource sampling misses transients; native telemetry/writer peaks unavailable; no new unavailability or policy breach reported; local truncation recovered in worker inventory',root_scope='Integrity/provenance/documentary routing only; root did not execute mathematical programs, solve or run formal tools',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r442-parent-integration.json',report)
den=json.loads((ROOT/'inherited-denials-r444.json').read_text());den['utc']=now
den['root_r442_scope']='Completed20 literal reviews,2authenticated public-source exclusions330282/356879,3sustained routes356624/342128/381465 retain exact global gaps; all0credit.11GET hops11payloads,no newdenial;1search3queries. All12frozen/all20rawbindings/actualmanifest verified. Fifteen reserved primary bodies unread. No formal routing.'
denpath=ROOT/'inherited-denials-r445.json';save(denpath,den)

base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=base_source[base_source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
peer_ids={326555,324571,332073};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406'}
for n in [443,444]:
 meta=json.loads((ROOT/f'selection-routing-r{n}.json').read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
L=P/'expanded-corpus-r445';assert not L.exists()
tail=tail.replace('selection-routing-r434.json','selection-routing-r445.json').replace('for num in range(421,434):','for num in range(421,443):')
tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active_peers))
tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60')
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2']:")
tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root separated this20 from all forty retained sibling IDs and all primary source URLs using root-owned metadata, without accessing sibling files. Also exclude accepted57 and held332073.')
tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes')\ntask=core+latest")
# Preserve the complete already-authorized latest routing, updating active peers and the completed pass.
previous=(ROOT/'intake-wavelet-r2-prepare-r444.py').read_text()
import ast
tree=ast.parse(previous);steering=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
steering=steering.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443','ACTIVE expanded-corpus-r443 and expanded-corpus-r444')
steering+='\nCompletedr442 all20 literals reviewed, all0credit.330282 actualMyers1504.03602v1T4.3/proof+T4.1/Cor4.2 bridge already refutes all cycle bounds;356879 actualHaythorpe2211.08105v1T1already publicly refutes full Hamiltoncycle bound,partialconstruction/figureaudit not newgraphcertificate.356624deBruijn alphabetmonotonicity does not lift wordlength; paddingfails; final2024positive-m theorem does not coverS0,2026shiftbodyunread.342128simplematroid density/triangle constraints do not pay fixed-k rankbound,uniform/parallelconnectiontrials failminimality;fixedfieldWQO not arbitrarymatroids.381465fullm reduction to exactnonabelianEGZ is ownpublicT7.2; quotient/coarsecurrent2026bound does not pay equality. Five reservedprimarybodies partially read, two successors,other15unread.11GETsuccess/no newdenial,1search3queries. Root all20raw/token/decodedbindings and frozen12verified; no independent mathematical clearance from metadata.\n'
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r445','exec'),ns)
rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
task=(L/'TASK.txt').read_text();assert 'Current55/60' not in task and 'wholelane maximum3 actual calls9' in task and 'Resources fixed:' in task
fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==12 and all(sha(Path(n))==v for n,v in fb.items()) and not (L/'bootstrap-receipt.json').exists()
save(ROOT/'r445-ready.json',dict(utc=now,accepted_new=57,target_new=60,completed_intake=str(P/'expanded-corpus-r442-parent-integration.json'),lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],latest_denials=str(denpath),active_peers=active_peers,model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,manifest_files=len(mf),original_bindings=len(bindings),frozen_bindings=12,receipt_exit_counts=report['receipt_exit_counts'],new_lane=str(L),ids=rr['ids'],task_sha256=sha(L/'TASK.txt'))))
