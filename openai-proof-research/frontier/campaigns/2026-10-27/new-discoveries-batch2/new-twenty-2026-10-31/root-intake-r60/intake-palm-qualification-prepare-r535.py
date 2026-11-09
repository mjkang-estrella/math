"""Root documentary verification and disposition of the 344875 independent qualification, and the r535 metadata packet on DeepSeek. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,collections,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==58 and led['target_new']==80
Q=P/'regular-palm-locating-primary-qualification-claude-r1';assert not (P/'expanded-corpus-r535').exists()

# Every documentary check precedes any root mutation.
m=read(Q/'MANIFEST.json');assert m['file_count']==150==len(m['files']) and m['credit']==0
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=Q/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
qex=sorted(m['terminal_self_exclusions']);assert set(qex)=={'MANIFEST.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
inventory=set()
for q in Q.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(Q)))
assert inventory==names|set(qex)
frozen(Q,22);qrec=receipts(Q,{'get_1.receipt.json':1,'scopes_acc_a.receipt.json':1,'scopes_acc_b.receipt.json':1,'scopes_acc_c.receipt.json':1,'scopes_acc_d.receipt.json':1,'scopes_acc_e.receipt.json':1})
assert sha(Q/'TASK.txt')==read(ROOT/'palm-qualification-r1-ready.json')['task_sha256']
qbudget=search(Q,2,2,2,6,['searches/search-1-full-response.txt','searches/search-2-full-response.txt'])
qe=guard(Q,[Q/f'plans/get-{i}.json' for i in range(1,6)],[344875],dict(attempt=5,success=4,unavailable=1),3)
un=next(e for e in qe if e['event']=='unavailable');assert 'iaeng.org/IJAM' in un['url']
review=read(Q/'review.json');assert set(review)=={'344875'};g=review['344875'];assert g['recommendation']=='EXCLUDE AS ROUTINE OR CORRECTION' and str(g['credit'])=='0'
for f in ['PROOF.md','REVIEW.md','source-map.json']:assert (Q/f).is_file()

qs='344875 independent adversarial qualification, Claude Opus 5.5: mathematics PASS with an independent reconstruction, literal PASS; recommendation EXCLUDE AS ROUTINE OR CORRECTION, moderate confidence. Theorem checked: chi_L(S_n(k)) = beta_k n^(1/k) + O_k(1) for fixed k>=2, so Conjecture 5.1 is false for every k>=4. ROOT ADOPTS EXCLUSION, credit 0, as a routine extension: the lower bound is the source p.11 count re-indexed plus AM-GM on the two parity classes, the construction is a routine variation of source Theorem 5.1 and the adjacent-position pattern with a short decoding argument, the printed constant is the uniform allocation, and the k=4 witness alone is coefficient tuning of the kind the user declined on 323531. This is a judgment call and the user may overrule; if so the only defensible unit is the all-k exact-constant theorem. Strongest dissent recorded: a deliberate printed conjecture is refuted at every k>=4 with the exact leading constant and a matching lower bound for every k, and no bridge from a published theorem exists; the exclusion rests on the source own argument. Bounded prior art: no earlier proof found; this is not a public-result finding. Unread lead: Amrullah et al. 2019, not treated as a hold. Verified 150 manifest files, 22 frozen bindings, 5 GET hops (3 PDF, 1 abstract page, 1 TLS failure), 2 searches.'
qr=dict(utc=now,mathdb_id=344875,source_lane=str(Q),manifest_sha256=sha(Q/'MANIFEST.json'),verified_manifest_files=150,verified_frozen_bindings=22,review=g,source_map=read(Q/'source-map.json'),runner_receipts=qrec,guard_events=dict(collections.Counter(e['event'] for e in qe)),search_budget=qbudget,scientific_summary=qs,reviewer_recommendation='EXCLUDE AS ROUTINE OR CORRECTION',root_disposition='EXCLUDE_ROUTINE_EXTENSION_OF_SOURCE_COUNT_USER_MAY_OVERRULE',credit=0,accepted_new=58,terminal_self_exclusions=qex,root_scope='Documentary integrity and scientific disposition only; no mathematics by root.')
save(P/'regular-palm-locating-qualification-parent-integration-r1.json',qr)
work='IAENG International Journal of Applied Mathematics 54(10) paper 09, title unknown'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after a TLS verification failure; no retry.'
den=read(ROOT/'inherited-denials-r567.json');den['utc']=now;den['root_palm344875_qualification_r1_scope']=qs;den['root_iaeng_tls_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un.get('url_key') or un['url']});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower()})
den['records'].append(dict(url=un['url'],reason=dict(status='TLS verification failure',artifact=work,restriction=fs),evidence=dict(path=str(Q/'guard-ledger.jsonl'),sha256=sha(Q/'guard-ledger.jsonl'),guard_sha256=sha(Q/'guard-ledger.jsonl'))))
denpath=ROOT/'inherited-denials-r568.json';save(denpath,den)
led['excluded_after_review']['344875']='regular-palm-locating-qualification-parent-integration-r1.json: mathematics PASS; root excluded as routine extension of the source count, user may overrule'
led['excluded_after_review']['352895']='expanded-corpus-r530-parent-integration.json: correct proof; root excluded as a source-ingredient extension of the source Dirichlet step, user may overrule'
(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')

base=read(ROOT/'r534-config.json');active=['expanded-corpus-r533','expanded-corpus-r534']
hist='The user has barred GPT subagents for now. Every mention of GPT-6.1 Sol, Codex or Sol-only in inherited text, and the file name model-policy-sol-only.json, is historical and does not apply to you. No children or fallback.'
note='\n'+qs+'\n'
base.update(number=535,model='spark/DeepSeek-V4.1-Flash-1017',reasoning='high',service='default',model_line='THIS LANE RUNS ON PI DEEPSEEK V4.1 FLASH, high thinking. '+hist+' A native web search tool is available in your environment; use the search budget for real prior-art checks and charge it before each call.',protected_peers=active,peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r534.json'}),denials=str(denpath),steering=base['steering']+note)
save(ROOT/'r535-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_models',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
print(json.dumps(dict(review_manifest=150,frozen=22,disposition=qr['root_disposition'],r535={k:r[k] for k in ['lane','ids','task_sha256','active_peers','model']},credit=0,accepted_new=58)))
