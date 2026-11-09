"""Root documentary verification of the independent 350767 review, root exclusion record, and r517 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
V=P/'digraph-aalpha-minimum-source-review-sol-r1';assert not (P/'expanded-corpus-r517').exists()

# Every documentary check precedes any root mutation.
vex=manifest(V,'SHA256-MANIFEST.json',139,'terminal_manifest_seal','exact_exclusions');frozen(V,30);vrec=receipts(V,{'scope_fields_all.receipt.json':1})
ready=read(ROOT/'digraph-aalpha-minimum-review-r1-ready.json');assert sha(V/'TASK.txt')==ready['task_sha256']
vbudget=search(V,2,6,2,6,['search-response1.json','search-response2.json']);ve=guard(V,[V/'get-prior1.json',V/'get-prior2.json'],[350767],dict(attempt=2,success=2),1)
review=read(V/'review.json');assert set(review)=={'350767'}
g=review['350767'];assert g['recommendation']=='EXCLUDE AS ROUTINE' and g['credit']==0 and g['gates']['ordinary'].startswith('PASS') and g['gates']['literal'].startswith('PASS') and g['gates']['significance']=='EXCLUDE AS ROUTINE recommended'
for f in ['PROOF.md','REVIEW.md','PRE-CANDIDATE.md','source-map.json','family-comparison.json','read-inventory.json']:assert (V/f).is_file()

vs='350767 independent ordinary PASS and cached-literal PASS for all n>=5 and 0<=alpha<1, with every arc table, short-chain boundary and directed isomorphism checked by hand; uniqueness is a proved strengthening not printed in Conjecture 3.7. ROOT SCIENTIFIC EXCLUDE AS ROUTINE, credit 0. Actual basis: the source Theorem 2.12 already orders bicyclic digraphs over the whole interval, the source structural reduction of Theorem 3.4 has no alpha<=1/2 step, and that restriction enters only in one final scalar estimate comparing G prime with the fourth theta on p10. Replacing that one estimate by a two-regime evaluation of the same polynomial at the same root completes the same proof with no new invariant, reduction, extremal type or parameter interaction, and the reviewer supplies the complete proof-level bridge. Li and Zhou arXiv 1305.0201v1 confirms the same architecture for alpha=0 in 2013, including the shortest cycle plus ear, the first exceptional arc table and the matching comparison. This is a routine-extension exclusion under campaign rules; it is NOT an authenticated earlier all-alpha solution, a novelty finding or a mathematical objection. Strongest dissent recorded: a deliberate source conjecture settled over the full remaining interval. Final source remains closed and unread; two searches and six strings found no later all-alpha resolution, which is not novelty clearance. All 96 supplied scopes compared, no family overlap. 139 manifest files, 30 frozen bindings verified; disclosed deviation: the first task and denial read omitted the outer timeout wrapper while the internal runner deadline remained; one documentary KeyError retained. Do not route to formal work.'
vr=dict(utc=now,mathdb_id=350767,source_lane=str(V),manifest_sha256=sha(V/'SHA256-MANIFEST.json'),verified_manifest_files=139,verified_frozen_bindings=30,verified_original_bindings=[350767],review=g,source_map=read(V/'source-map.json'),runner_receipts=vrec,guard_events=dict(collections.Counter(e['event'] for e in ve)),search_budget=vbudget,scientific_summary=vs,reviewer_recommendation='EXCLUDE AS ROUTINE',root_disposition='SCIENTIFIC_EXCLUDE_ROUTINE_EXTENSION_ORDINARY_PASS_RETAINED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=vex,root_scope='Documentary integrity and root scientific disposition only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r534.json');den['utc']=now;den['root_digraph350767_review_scope']=vs
save(P/'digraph-aalpha-minimum-review-parent-integration-r1.json',vr);denpath=ROOT/'inherited-denials-r535.json';save(denpath,den)

base=read(ROOT/'r516-config.json');active=['high-girth-ur-matching-formal-sol-r6','expanded-corpus-r516']
base.update(number=517,protected_peers=active,peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r6.json','selection-routing-r516.json','selection-routing-parking-strong-a2-formal-r1.json'],denials=str(denpath))
base['steering']+='\n'+vs+'\nRoot continues uncredited 338806 formal research r6, not a scientific PASS, acceptance or source waiver; all formal bodies and flat metadata are protected from discovery. r516 is active and entirely protected. 57/60 unchanged.\n'
save(ROOT/'r517-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r517=module.prepare(base)
for name in read(Path(r517['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r517['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'digraph-exclude-r517-next-routing.json',dict(utc=now,excluded=dict(mathdb_id=350767,disposition=vr['root_disposition']),discovery=r517,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(review_manifest=139,frozen=30,excluded=350767,r517=r517,credit=0,accepted_new=57)))
