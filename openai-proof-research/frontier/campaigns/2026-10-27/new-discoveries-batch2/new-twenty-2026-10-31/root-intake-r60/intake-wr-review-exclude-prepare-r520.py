"""Root documentary verification of the independent 341690 review, root exclusion record, and r520 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
V=P/'widom-rowlinson-tisgm-source-review-sol-r1';assert not (P/'expanded-corpus-r520').exists()

# Every documentary check precedes any root mutation.
vex=manifest(V,'seal-manifest.json',153,'seal_own_manifest','terminal_non_circular_exclusions');frozen(V,32);vrec=receipts(V,{'get_hinge.receipt.json':1})
ready=read(ROOT/'widom-rowlinson-review-r1-ready.json');assert sha(V/'TASK.txt')==ready['task_sha256']
vbudget=search(V,2,6,2,6,['search-1-response.json','search-2-response.json']);ve=guard(V,[V/n for n in ['get-hinge.json','get-later.json','get-later-body.json']],[341690],dict(attempt=3,success=2,unavailable=1),1)
un=next(e for e in ve if e['event']=='unavailable');assert un['status']==404 and 'mathnet.uz' in un['url']
review=read(V/'review.json');assert set(review)=={'341690'};g=review['341690'];assert g['recommendation']=='EXCLUDE AS ROUTINE OR KNOWN' and g['credit']==0 and g['gates']['ordinary']=='PASS' and g['gates']['literal'].startswith('PASS')
for f in ['PROOF.md','REVIEW.md','source-map.json','family-comparison.json','read-visual-access-inventory.json','NEW-UNAVAILABLE-REVIEW.json']:assert (V/f).is_file()

vs='341690 independent ordinary PASS and cached-literal PASS with an explicit stronger partition: exact one-versus-three TISGM counts for the ferromagnetic hard-core and soft-core Widom-Rowlinson model for all k>=4, Gibbs-measure bridge supplied and valid at theta=0. ROOT SCIENTIFIC EXCLUDE AS ROUTINE, credit 0. Actual basis: arXiv 2401.08706v1 Theorem 3 gives the exact hard-core hinge count, which already forces injectivity and hence strict monotonicity of the theta=0 branch function; the positive-theta case differs only by the elementary positive increasing factor 1/(1-theta/R) and truncation of the interval, and the reviewer supplies the complete all-parameter reduction. Stated limits: this is a routine-adaptation exclusion, not an earlier printed soft-core theorem and not a novelty finding; the upstream hinge proof is abbreviated though its conclusion was independently validated; Rozikov-Khakimov 2015 returned HTTP 404 and is closed and unread; the 2019 final remains closed and unread; source Remark 2 reverses a critical inequality, with no credit for that. Strongest dissent recorded: a deliberate conjecture and an elegant global convexity argument. Formal cost is also high, since the literal needs infinite-tree Gibbs infrastructure. All 96 supplied scopes compared, no family overlap. 153 manifest files, 32 frozen bindings verified. Do not route to formal work.'
work='Rozikov and Khakimov, Queueing Systems 81 (2015) 49-69, DOI 10.1007/s11134-015-9450-1'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 404 at the observed primary PDF URL; no retry. Distinct later papers such as arXiv 2401.08706 are not denied.'
vr=dict(utc=now,mathdb_id=341690,source_lane=str(V),manifest_sha256=sha(V/'seal-manifest.json'),verified_manifest_files=153,verified_frozen_bindings=32,verified_original_bindings=[341690],review=g,source_map=read(V/'source-map.json'),runner_receipts=vrec,guard_events=dict(collections.Counter(e['event'] for e in ve)),search_budget=vbudget,new_unavailable=read(V/'NEW-UNAVAILABLE-REVIEW.json'),scientific_summary=vs,reviewer_recommendation='EXCLUDE AS ROUTINE OR KNOWN',root_disposition='SCIENTIFIC_EXCLUDE_ROUTINE_ADAPTATION_ORDINARY_PASS_RETAINED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=sorted(vex),root_scope='Documentary integrity and root scientific disposition only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r544.json');den['utc']=now;den['root_wr341690_review_scope']=vs;den['root_wr_hinge_2015_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key'],'doi.org/10.1007/s11134-015-9450-1'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'10.1007/s11134-015-9450-1'})
den['records'].append(dict(url=un['url'],reason=dict(status=404,artifact=work,restriction=fs),evidence=dict(path=str(V/'NEW-UNAVAILABLE-REVIEW.json'),sha256=sha(V/'NEW-UNAVAILABLE-REVIEW.json'),guard_sha256=sha(V/'guard-ledger.jsonl'))))
save(P/'widom-rowlinson-review-parent-integration-r1.json',vr);denpath=ROOT/'inherited-denials-r545.json';save(denpath,den)

base=read(ROOT/'r519-config.json');active=['interval-kwidth-formal-sol-r1','simplex-three-design-primary-qualification-sol-r2']
base.update(number=520,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{518,519}),peer_routing_files=['selection-routing-interval-kwidth-formal-r1.json','selection-routing-simplex-three-design-qualification-r2.json','selection-routing-parking-strong-a2-formal-r1.json','selection-routing-high-girth-ur-matching-formal-r8.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{336276,341690,362896});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/1706.01230','https://arxiv.org/abs/1901.09258','https://arxiv.org/abs/2404.18847'})
for name in ['expanded-corpus-r518-parent-integration.json','expanded-corpus-r519-parent-integration.json','interval-kwidth-review-parent-integration-r1.json','simplex-three-design-review-parent-integration-r1.json']:base['steering']+='\n'+read(P/name)['scientific_summary']
base['steering']+='\n'+vs+'\n'+read(P/'high-girth-ur-matching-formal-parent-integration-r8.json')['scientific_summary']+'\nActive and entirely protected: the 336276 formal lane and the 362896 second qualification. 323531 and 338806 stay under scientific hold with Lean paused. 57/60 unchanged.\n'
save(ROOT/'r520-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r520=module.prepare(base)
for name in read(Path(r520['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r520['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'wr-exclude-r520-next-routing.json',dict(utc=now,excluded=dict(mathdb_id=341690,disposition=vr['root_disposition']),discovery=r520,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(review_manifest=153,frozen=32,excluded=341690,r520=r520,credit=0,accepted_new=57)))
