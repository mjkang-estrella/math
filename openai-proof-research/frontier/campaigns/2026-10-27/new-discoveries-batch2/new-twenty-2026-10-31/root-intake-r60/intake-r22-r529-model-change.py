"""Root documentary verification of 382297 formal r22 and discovery r529, the user's model change, and target-80 packet tooling for Claude and DeepSeek lanes. No root Lean or mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,re,collections
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
F=P/'transitive-bunkbed-state-dominance-formal-sol-r22';A=P/'expanded-corpus-r529';pins=read(F/'PINS.json')
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# r22: every documentary check precedes any root mutation.
fex=manifest(F,'MANIFEST.json',220,'seal_manifest','terminal_noncircular_self_exclusions');frozen(F,63)
assert sha(F/'TASK.txt')==read(ROOT/'bunkbed-dominance-r22-ready.json')['task_sha256']
expected={n+'.receipt.json':1 for n in ['actual_v1','actual_v2','compress_probe1','dominance_v1','dominance_v2','dominance_v3','final_v1','final_v2','final_v3','final_v4','law_v1','law_v2','payoff_v1','payoff_v2','rows_v1','rows_v2','rows_v3','rows_v4','rows_v5','rows_v6','rows_v7','sums_v2','sums_v3']}
frec=[];G6=6*1024**3;G32=32*1024**3
for q in sorted(F.glob('*.receipt.json')):
 v=read(q);lean='formal_command.py' in ' '.join(v['command'])
 assert v['cwd']==str(F) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 assert v['exit']==expected.get(q.name,0),(q.name,v['exit']);frec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
result=read(F/'results/382297.json');green=result['strict_green_modules'];assert len(green)==28 and result['final_theorem_proven'] is True and result['final_theorem']=='Bun.state_endpoint' and result['unpaid']==[]
base={x['name']:x for x in read(F/'BASELINE.json')['immutable_green_modules']};assert len(base)==20
new=['BunDomRows','BunDomFiberSums','BunDomActualCounts','BunDomCountLaw','BunDomCompressed','BunDomDominance','BunDomPayoff','BunDomFinal']
assert {x['name'] for x in green}==set(base)|set(new)
trio={'propext','Classical.choice','Quot.sound'}
for row in green:
 m=row['name'];s=sha(F/'src'/(m+'.lean'));o=sha(F/'build'/(m+'.olean'));assert s==row['source_sha256'] and o==row['olean_sha256'],m
 assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',(F/'src'/(m+'.lean')).read_text(),re.M),m
 if m in base:assert s==base[m]['source_sha256'] and o==base[m]['olean_sha256'],m;continue
 c=next(x for x in jsonrows(F/(row['compile_label']+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(F/(row['check_label']+'.output.txt')) if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(F/(row['compile_label']+'.receipt.json'))['exit']==read(F/(row['check_label']+'.receipt.json'))['exit']==0,m
 assert s==c['source_sha256_after']==k['source_sha256_after'] and o==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
audit=(F/'audit_all_r22.output.txt').read_text(errors='replace');found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit);assert len(found)==30 and all({y.strip() for y in f[1].split(',')}<=trio for f in found) and any(f[0]=='Bun.state_endpoint' for f in found);assert read(F/'audit_all_r22.receipt.json')['exit']==0
final=(F/'src/BunDomFinal.lean').read_text();assert re.search(r'theorem state_endpoint : ∀ \(n u j : Nat\), u ≤ j → j < n →\s+Fintype\.card \{w : Bun\.Asg n j // j ∈ Bun\.sval true \(Bun\.stf n u j w\)\} ≤\s+Fintype\.card \{w : Bun\.Asg n j // j ∈ Bun\.sval false \(Bun\.stf n u j w\)\}',final)

# r529.
m=read(A/'MANIFEST.json');assert len(m['files'])==177
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','terminal_manifest_seal.receipt.json','terminal_manifest_seal.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r529.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'EXACT20-GATES.json');bind=read(A/'corpus-bindings.json');assert len(ids)==len(gates)==len(bind)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in bind}
sources={}
for v in bind:
 key=str(v['id']);raw,obj,token=corpus(dict(v,line=int(v['line'])));assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['statement_utf8'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'];sources[key]=obj['source_url']
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-response-1.json','search-response-2.json','search-response-3.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=5,success=5),4)
shell=next(e for e in ae if e['event']=='success' and 'dspace.mic.ul.ie' in e['url'])
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==928 and {x['path'] for x in hist}==set(allow)
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482])

# Root records, after all checks.
fs='382297 uncredited formal r22 COMPLETE FOR ITS SCOPE. Root verified from receipts: Bun.state_endpoint, for all n u j with u<=j<n, the number of window assignments with j in the layer-true state set is at most the number with j in the layer-false set, with no added premise. Eight new modules (Rows, FiberSums, ActualCounts, CountLaw, Compressed, Dominance, Payoff, Final) have compile, kernel and hash evidence on top of twenty sealed modules, and thirty audited theorems use only propext, Classical.choice and Quot.sound. Twenty-three failed compile attempts retained with true exits. Unpaid for the campaign: the literal Reach bridge, the window-to-full-outcome factor, the literal endpoint theorem, a fresh empty-build replay of the whole chain, independent formal audit and paper. Credit 0, 57/80. 220 manifest files, 63 frozen bindings.'
fr=dict(utc=now,mathdb_id=382297,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=220,verified_frozen_bindings=63,green_modules=green,new_modules=new,runner_receipts=frec,result=result,scientific_summary=fs,root_disposition='STATE_ENDPOINT_KERNEL_CHECKED_UNCREDITED_ASSEMBLY_NEXT',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity only; no Lean by root.')
save(P/'transitive-bunkbed-state-dominance-formal-parent-integration-r22.json',fr)
ass='r529 zero qualified survivors, no candidate. 375405 is publicly refuted by Li, Ling, Sun and Zhu, arXiv 2610.19965v1, with a complete bridge to the negation, zero. 359050 keeps an author-complete partial base-locus lemma; 363818 keeps three routes without the sharp classification. Lonely Runner, shifted Lonely Runner, Zaremba, weak Atiyah and Skolem parked without effort. 363172: the selected route returned a JavaScript shell and the whole work is closed. Seventeen assigned source works unread; recorded parks are not open-status certifications. Verified 177 manifest files, 20 corpus bindings, 13 frozen, 928 saved history entries, 5 GET hops (4 PDF, 1 non-paper shell), 3 searches / 9 strings with responses saved. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=177,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=928,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
save(P/'expanded-corpus-r529-parent-integration.json',ar)
work='Groups of singular alternating sign matrices, arXiv 2405.13611, EJLA 41 (2025) 288-303, DOI 10.13001/ela.2025.8715'
fsc=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after the observed route returned a 1107-byte JavaScript shell; no retry.'
den=read(ROOT/'inherited-denials-r562.json');den['utc']=now;den['root_r529_scope']=ass;den['root_asm_shell_closure']=fsc
den['blocked_keys']=sorted(set(den['blocked_keys'])|{shell.get('url_key') or shell['url'],'arxiv.org/abs/2405.13611','arxiv.org/pdf/2405.13611'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'2405.13611','10.13001/ela.2025.8715'})
den['records'].append(dict(url=shell['url'],reason=dict(status='200 non-paper shell',artifact=work,restriction=fsc),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
den['root_user_model_change_20261109']='User: do not use GPT as a subagent for now; use Claude Opus 5.5 and multiple DeepSeek for subagents.'
save(ROOT/'inherited-denials-r563.json',den)
policy=dict(utc=now,user_instruction='do not use gpt as a subagent for now; use claude opus 5.5 and multiple deepseek for subagents',allowed=[dict(provider='claudeAgent',model='claude-opus-5-5',options=dict(effort='high',fastMode=False)),dict(provider='pi',model='spark/DeepSeek-V4.1-Flash-1017',options=dict(thinking='high'))],barred=['codex gpt-6.1-sol and every other GPT model, for now'],supersedes='GPT-6.1 Sol routing of 2026-11-07 and 2026-11-08',concurrency_cap=3)
save(ROOT/'model-policy-claude-deepseek-20261109.json',policy)
led['model_allocation_history'].append(dict(utc=now,previous=led['model_allocation_update']));led['model_allocation_update']=policy
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='second adversarial qualification PASS; root prospective scientific pass; Bun.state_endpoint kernel-checked (r22); Reach bridge, window factor, literal endpoint, replay, formal audit and paper unpaid; credit 0'
led['process_notes'].append(dict(utc=now,item='User barred GPT subagents for now; Claude Opus 5.5 and DeepSeek only. r22 had already finished before a cancel was sent, so no GPT lane was interrupted.'))
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
with (P/'AGENTS.md').open('a') as q:q.write("\nModel note 2026-11-09: the user says do not use GPT as a subagent for now; use Claude Opus 5.5 and multiple Pi DeepSeek (`spark/DeepSeek-V4.1-Flash-1017`) subagents. This supersedes earlier GPT-6.1 Sol routing. The three-delegate cap stands.\n")

# Packet tooling.
old=(ROOT/'prepare_discovery_packet_target80.py').read_text()
reps=[("total. ONLYGPT-6.1Solhigh/default ALLagents,nochildren/fallback. Root orch","total. '+config['model_line']+' Root orch"),("model='gpt-6.1-sol',reasoning='high',service='default',latest_denia","model=config['model'],reasoning=config['reasoning'],service=config['service'],latest_denia"),
(" namespace=dict(globals())"," tail=tail.replace(\"'model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default'\",\"'model':\"+repr(config['model'])+\",'reasoning_effort':\"+repr(config['reasoning'])+\",'service_tier':\"+repr(config['service']))\n namespace=dict(globals())")]
new_text=old
for a,b in reps:
 assert new_text.count(a)==1,a;new_text=new_text.replace(a,b)
C=ROOT/'prepare_discovery_packet_models.py';assert not C.exists();C.write_text('# Root 2026-11-09: target-80 constructor with the model line and routing fields taken from config; GPT barred by the user.\n'+new_text)
print(json.dumps(dict(r22_manifest=220,frozen=63,green=28,new=len(new),audited=len(found),r529_manifest=177,constructor_sha=sha(C),credit=0,accepted_new=57)))
