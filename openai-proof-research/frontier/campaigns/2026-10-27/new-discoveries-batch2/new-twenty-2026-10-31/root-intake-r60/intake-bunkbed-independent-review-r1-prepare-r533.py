"""Root documentary verification of the 382297 independent final formal review and the r533 metadata packet. No root Lean or mathematics."""
import os,resource,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,re,collections,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
R=P/'transitive-bunkbed-formal-independent-review-claude-r1';pins=read(R/'PINS.json');G6=6*1024**3;G32=32*1024**3;trio={'propext','Classical.choice','Quot.sound'}
assert not (P/'expanded-corpus-r533').exists()
def jsonrows(q):
 out=[]
 for line in q.read_text(errors='replace').splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out

# Every documentary check precedes any root mutation.
fex=manifest(R,'MANIFEST.json',389,'seal_manifest','terminal_noncircular_self_exclusions');frozen(R,61)
rdy=read(ROOT/'bunkbed-independent-review-r1-ready.json');assert sha(R/'TASK.txt')==rdy['task_sha256'] and sha(R/'packet/382297-source-only.zip')==rdy['packet_sha256']
expected={'control_e_v1.receipt.json':1};rrec=[]
for q in sorted(R.glob('*.receipt.json')):
 v=read(q);cmd=' '.join(v['command']);lean='runpy.run_path' in cmd and 'FORMAL_ROOT' in cmd
 assert v['cwd']==str(R) and v['cpu_limit_s']==115 and v['group_rss_guard_bytes']==G6 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
 assert v['as_limit_bytes']==(G32 if lean else G6),q.name
 assert v['exit']==expected.get(q.name,0),(q.name,v['exit']);rrec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
order=read(R/'packet/BUILD-ORDER.json');hashes=read(R/'packet/SOURCE-HASHES.json');assert len(order)==33==len(hashes)
fresh=read(R/'results/FRESH-REPLAY.json');assert fresh['count']==33 and fresh['all_zero'] is True and {x['module'] for x in fresh['modules']}==set(order)
for row in fresh['modules']:
 m=row['module'];assert row['compile_exit']==row['check_exit']==0,m
 c=next(x for x in jsonrows(R/f'fresh_compile_{m}.output.txt') if x.get('stage')=='compile' and x.get('module')==m);k=next(x for x in jsonrows(R/f'fresh_check_{m}.output.txt') if x.get('stage')=='check' and x.get('module')==m)
 assert c['exit']==k['exit']==0 and read(R/f'fresh_compile_{m}.receipt.json')['exit']==read(R/f'fresh_check_{m}.receipt.json')['exit']==0,m
 s=sha(R/'src'/(m+'.lean'));o=sha(R/'build'/(m+'.olean'));assert s==hashes[m]==c['source_sha256_after']==k['source_sha256_after'] and o==row['olean_sha256']==c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after'],m
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],m] and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1,m
review=read(R/'review.json');assert set(review)=={'382297'};g=review['382297'];assert g['recommendation']=='TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING' and g['defects_affecting_validity_or_fidelity'] in (0,'0') and str(g['credit'])=='0'
gates=g['gates'];assert all(gates[k]['result'].startswith('PASS') for k in gates if k[0] in 'ABCDE'),gates
closure=[x for x in R.glob('*.output.txt') if "'Bun.bunkbed_E7_transitive' depends on axioms" in x.read_text(errors='replace')];assert closure
for q in closure:
 found=re.findall(r"'Bun\.bunkbed_E7_transitive' depends on axioms: \[([^\]]*)\]",q.read_text(errors='replace'));assert all({y.strip() for y in f.split(',')}<=trio for f in found),q.name
assert (R/'FINAL-REVIEW.md').is_file() and (R/'src/ControlE.lean').is_file() and (R/'src/AuditClosure.lean').is_file()
abudget=search(R,2,2,2,4,['search/response-1.txt','search/response-2.txt']) if False else read(R/'search-budget.json');assert abudget==dict(calls_used=2,queries_used=2,maximum_calls=2,maximum_queries=4,charged_before_call=True)
charges=[json.loads(s) for s in (R/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2 and all(sha(R/c['plan'])==c['plan_sha256'] for c in charges) and all(len((R/f'search/response-{i}.txt').read_text())>1000 for i in (1,2))
head=subprocess.run(['git','-C',pins['packages_root']+'/mathlib','rev-parse','HEAD'],capture_output=True,text=True).stdout.strip();assert head==pins['mathlib_revision']=='d13f23b723b8a846827a245b89c10fc7d3f11612'

rs='382297 independent final formal review, Claude Opus 5.5: TECHNICAL_PASS_ROOT_ADJUDICATION_PENDING. Root verified from receipts a fresh extraction of the sealed 33-module packet with hash matches and 33 compiles and 33 kernel checks from an empty build. The reviewer read all 33 modules, found no sorry, axiom, unsafe or metaprogramming construct and no conclusion-bearing premise; the transitive closure of 6913 constants has only propext, Classical.choice and Quot.sound with 0 unsafe and 0 partial; statement fidelity passed against arXiv Model 4.5 and Conjecture 6.4, the journal D7 and the MathDB literal, with Lean controls giving 1 and 2 at n=1, 7 and 9 of 16 at n=2, the swapped inequality false, and one shared vertical token. Root confirmed the mathlib checkout at the pinned revision. Bounded prior art found no match in two searches; no bodies fetched. Four cosmetic or low defects, none affecting validity or fidelity. Limits retained: the closed acyclic final is unread, upstream oleans are trusted, the relabeling of an abstract transitive tournament to Fin n is not formalized and is trivial, and family comparison was a spot check. Disclosed: display filters and one scratchpad edit ran outside the runner and touched no lane file. Paper and root adjudication unpaid. Credit 0, 57/80. 389 manifest files, 61 frozen bindings.'
rr=dict(utc=now,mathdb_id=382297,source_lane=str(R),manifest_sha256=sha(R/'MANIFEST.json'),verified_manifest_files=389,verified_frozen_bindings=61,packet_sha256=rdy['packet_sha256'],fresh_replay_modules=33,review=g,runner_receipts=rrec,search_budget=abudget,mathlib_head_verified=head,scientific_summary=rs,root_disposition='TECHNICAL_PASS_ADOPTED_PENDING_PAPER_AND_ROOT_ADJUDICATION',credit=0,accepted_new=57,terminal_self_exclusions=sorted(fex),root_scope='Documentary integrity and read-only pin check; no Lean by root.')
save(P/'transitive-bunkbed-formal-independent-review-parent-integration-r1.json',rr)
den=read(ROOT/'inherited-denials-r566.json');den['utc']=now;den['root_bunkbed_independent_review_r1_scope']=rs;denpath=ROOT/'inherited-denials-r567.json';save(denpath,den)
for c in led['candidates']:
 if int(c['mathdb_id'])==382297:c['status']='literal Lean endpoint kernel-checked; independent final formal review TECHNICAL PASS (Claude Opus 5.5), root verified; paper and root adjudication pending; credit 0';c['independent_formal_review']='transitive-bunkbed-formal-independent-review-parent-integration-r1.json'
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')

base=read(ROOT/'r532-config.json');active=['transitive-bunkbed-manuscript-deepseek-r1','regular-palm-locating-primary-qualification-claude-r1']
note='\n'+read(P/'expanded-corpus-r531-parent-integration.json')['scientific_summary']+'\n'+read(P/'expanded-corpus-r532-parent-integration.json')['scientific_summary']+'\nThe structured-family ranking continues.\n'
base.update(number=533,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{531,532}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r532.json','selection-routing-palm-qualification-r1.json','selection-routing-bunkbed-independent-review-r1.json'}),denials=str(denpath),steering=base['steering']+note)
save(ROOT/'r533-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_models',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps(dict(review_manifest=389,frozen=61,fresh=33,mathlib=head,r533={k:r[k] for k in ['lane','ids','task_sha256','active_peers','model']},credit=0,accepted_new=57)))
