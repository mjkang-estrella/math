"""Root documentary verification of the independent 352259 review, root PARK record, and r515 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
V=P/'nfm-dirichlet-psd-source-review-sol-r1';assert not (P/'expanded-corpus-r515').exists()

# Every documentary check precedes any root mutation.
m=read(V/'manifest.json');files=m['files'];rows=list(files.items()) if isinstance(files,dict) else [(x['path'],x) for x in files];assert len(rows)==84==m['file_count'] and m['credit']==0
names=set()
for n,x in rows:
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=V/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
vex=sorted(m['terminal_noncircular_self_exclusions']);assert set(vex)=={'manifest.json','terminal_seal.receipt.json','terminal_seal.output.txt'}
inventory=set()
for q in V.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(V)))
assert inventory==names|set(vex)
frozen(V,33);vrec=receipts(V,{'initial_read.receipt.json':1})
ready=read(ROOT/'nfm-dirichlet-psd-review-r1-ready.json');assert sha(V/'TASK.txt')==ready['task_sha256']
assert read(V/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True) and not (V/'guard-ledger.jsonl').exists() and not (V/'search-charges.jsonl').exists()
review=read(V/'review.json');assert set(review)=={'352259'}
g=review['352259'];assert g['recommendation']=='PARK' and g['credit']==0 and g['formal_dispatch'] is False and g['children']==0
for f in ['PROOF.md','REVIEW.md','source-map.json','family-comparison.json','inventory.json']:assert (V/f).is_file()

vs='352259 independent ordinary PASS for every fixed finite k>=2 and every finite strictly positive alpha, under the intended nonempty-witness reading of Theorem 3.4; PSD energy consequence independently sound; no full-graph recovery claim. ROOT SCIENTIFIC PARK, credit 0. Literal binding unresolved: the literal cites Theorem 2 where v1 prints Theorem 3.4, k=1 has infinite logits though Definition 2.1 allows it, and the printed Theorem 3.4 omits nonempty S, which would otherwise make it vacuous; label and domain repairs earn zero credit. Significance: the reviewer gives a complete source-to-target application from Theorem 3.4 and the Example 3.1 concentration method, with no new invariant, and an alpha-dependent threshold with no quantitative guarantee; root treats this as a substantive routine-application objection, not a shortness objection and not an authenticated earlier public result. Prior art: Waterloo dissertation Chapter 5 remains specifically unread at a forbidden /server/api/ URL, identity and date unauthenticated; no fresh later, journal or citing-work check was made because the reviewer did not complete a personal read of the inherited denials and issued zero GETs and zero searches. That is a limitation of the review, not a transport denial, and those works are not closed. All 96 supplied scopes compared, no family match. Formal gate unpaid and not dispatched. 84 manifest files, 33 frozen bindings verified; one documentary read failure retained. Do not resurrect without a new specific significance argument or reading the dissertation chapter by a permitted delivery.'
vr=dict(utc=now,mathdb_id=352259,source_lane=str(V),manifest_sha256=sha(V/'manifest.json'),verified_manifest_files=84,verified_frozen_bindings=33,verified_original_bindings=[352259],review=g,source_map=read(V/'source-map.json'),runner_receipts=vrec,search_budget=read(V/'search-budget.json'),fresh_network_requests=0,scientific_summary=vs,root_disposition='SCIENTIFIC_PARK_ROUTINE_APPLICATION_OBJECTION_SPECIFIC_UNREAD_DISSERTATION',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=vex,root_scope='Documentary integrity and root scientific disposition only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r529.json');den['utc']=now;den['root_nfm352259_review_scope']=vs
save(P/'nfm-dirichlet-psd-review-parent-integration-r1.json',vr);denpath=ROOT/'inherited-denials-r530.json';save(denpath,den)

base=read(ROOT/'r514-config.json');active=['high-girth-ur-matching-formal-sol-r5','parking-strong-a2-source-review-sol-r1']
base.update(number=515,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{513,514}),peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r5.json','selection-routing-parking-strong-a2-review-r1.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{352259,323531});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/2110.08385','https://arxiv.org/abs/1205.4293'})
for name in ['high-girth-ur-matching-formal-parent-integration-r4.json','expanded-corpus-r513-parent-integration.json','expanded-corpus-r514-parent-integration.json','nfm-dirichlet-psd-review-parent-integration-r1.json']:base['steering']+='\n'+read(P/name)['scientific_summary']
base['steering']+='\nRoot continues uncredited 338806 formal research r5, not a scientific PASS, acceptance or source waiver; all formal bodies and flat metadata are protected from discovery. 323531 is in active independent review and entirely protected. 352259 is SCIENTIFIC PARK. The entire work arXiv 1205.4293, all versions and its J. Algebraic Combinatorics 40(2) (2014) 417-473 final is closed to all new deliveries including query, metadata, hosts, versions, cache, mirror, DOI, API and indirect recovery. Distinct papers are not blanket denied. 57/60 unchanged.\n'
save(ROOT/'r515-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r515=module.prepare(base)
for name in read(Path(r515['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r515['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'nfm-review-park-r515-next-routing.json',dict(utc=now,park=dict(mathdb_id=352259,disposition=vr['root_disposition']),discovery=r515,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(review_manifest=84,frozen=33,park=352259,r515=r515,credit=0,accepted_new=57)))
