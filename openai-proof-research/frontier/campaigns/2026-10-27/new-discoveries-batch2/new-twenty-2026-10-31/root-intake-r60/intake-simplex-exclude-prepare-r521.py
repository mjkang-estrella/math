"""Root documentary verification of the 362896 second qualification, root exclusion record, and r521 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
V=P/'simplex-three-design-primary-qualification-sol-r2';assert not (P/'expanded-corpus-r521').exists()

# Every documentary check precedes any root mutation.
vex=manifest(V,'SHA256-MANIFEST.json',169,'seal','terminal_exclusions');frozen(V,51);vrec=receipts(V,{'scopes_accepted_c_prior_a.receipt.json':1,'get_flatto_primary.receipt.json':1,'inventories_and_validation.receipt.json':1})
ready=read(ROOT/'simplex-three-design-qualification-r2-ready.json');assert sha(V/'TASK.txt')==ready['task_sha256']
vbudget=search(V,2,6,2,6,['search-response-1.json','search-response-2.json']);ve=guard(V,[V/'get-fialkow.json',V/'get-flatto-primary.json'],[362896],dict(attempt=2,success=1,unavailable=1),1)
un=next(e for e in ve if e['event']=='unavailable');assert un['status']==403 and 'sciencedirect' in un['url']
review=read(V/'review.json');assert set(review)=={'362896'};g=review['362896'];assert g['recommendation']=='EXCLUDE AS ROUTINE OR KNOWN' and g['credit']==0 and g['gates']['ordinary'].startswith('PASS') and g['gates']['literal'].startswith('PASS') and 'ROUTINE' in g['basis']
for f in ['PROOF.md','REVIEW.md','source-map.json','family-comparison.json','read-inventory.json','NEW-UNAVAILABLE-REVIEW.json']:assert (V/f).is_file()

vs='362896 second focused qualification: equal-weight ordinary proof PASS for every d>=3 and cached-literal PASS. ROOT SCIENTIFIC EXCLUDE AS ROUTINE, credit 0, routine branch and not an authenticated exact public-proof exclusion. Actual basis: there is no d-node degree-three formula on the flat (d-1)-simplex even with free real weights. Exactness through degree two makes affine evaluation invertible and forces positive weights; exactness through degree three simultaneously diagonalizes the compressed affine multiplication operators, and the first three simplex moments give a nonzero commutator as soon as d>=3. That is the classical minimal Gaussian-cubature regime; the Gaussian common-zero criterion was authenticated in Fialkow and Petrovic, and the reviewer supplies the complete reduction, so the equal-weight restriction does no essential work. Flatto and Haber 1973, A quadrature formula of degree three, is reported by an indexed abstract to state minimum n+2 nodes for an n-simplex with free coefficients; its body returned HTTP 403 and is closed and unread, so it is a precise historical HOLD and is not used as the basis. Fritsch 1970 and the fingerprint-only Xu work also remain closed and unread. Source defects recorded with no credit: printed Appendix B.1 Eq. 48 does not match its stated cost, and Appendix D symmetry reduction has a gap though its conclusion is correct. The true predecessor reference is Baladram, Interdisciplinary Information Sciences 24 (2018), and 1308.3188 is Cohn, Kumar and Minton. Strongest dissent recorded: a deliberate 2025 all-dimension conjecture with a rotation-independent tensor proof. All 96 supplied scopes compared, no family overlap. 169 manifest files, 51 frozen bindings verified; three documentary failures retained. Do not route to formal work.'
work='Flatto and Haber, A quadrature formula of degree three, 1973, ScienceDirect PII 002190457390110X'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/author/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 403 before any body; no retry. Its theorem and proof remain unread. Other cubature works are not blanket denied.'
vr=dict(utc=now,mathdb_id=362896,source_lane=str(V),manifest_sha256=sha(V/'SHA256-MANIFEST.json'),verified_manifest_files=169,verified_frozen_bindings=51,verified_original_bindings=[362896],review=g,source_map=read(V/'source-map.json'),runner_receipts=vrec,guard_events=dict(collections.Counter(e['event'] for e in ve)),search_budget=vbudget,new_unavailable=read(V/'NEW-UNAVAILABLE-REVIEW.json'),scientific_summary=vs,reviewer_recommendation='EXCLUDE AS ROUTINE OR KNOWN',root_disposition='SCIENTIFIC_EXCLUDE_ROUTINE_CLASSICAL_GAUSSIAN_SPECIALIZATION_ORDINARY_PASS_RETAINED',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=sorted(vex),root_scope='Documentary integrity and root scientific disposition only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r545.json');den['utc']=now;den['root_simplex362896_qualification_r2_scope']=vs;den['root_simplex_flatto_haber_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key']});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'002190457390110x'})
den['records'].append(dict(url=un['url'],reason=dict(status=403,artifact=work,restriction=fs),evidence=dict(path=str(V/'NEW-UNAVAILABLE-REVIEW.json'),sha256=sha(V/'NEW-UNAVAILABLE-REVIEW.json'),guard_sha256=sha(V/'guard-ledger.jsonl'))))
save(P/'simplex-three-design-qualification-parent-integration-r2.json',vr);denpath=ROOT/'inherited-denials-r546.json';save(denpath,den)

base=read(ROOT/'r520-config.json');active=['interval-kwidth-formal-sol-r1','expanded-corpus-r520']
base.update(number=521,protected_peers=active,peer_routing_files=['selection-routing-interval-kwidth-formal-r1.json','selection-routing-r520.json','selection-routing-parking-strong-a2-formal-r1.json','selection-routing-high-girth-ur-matching-formal-r8.json'],denials=str(denpath))
base['steering']+='\n'+vs+'\nActive and entirely protected: the 336276 formal lane and r520. 323531 and 338806 stay under scientific hold with Lean paused. 57/60 unchanged.\n'
save(ROOT/'r521-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r521=module.prepare(base)
for name in read(Path(r521['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r521['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'simplex-exclude-r521-next-routing.json',dict(utc=now,excluded=dict(mathdb_id=362896,disposition=vr['root_disposition']),discovery=r521,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(qualification_manifest=169,frozen=51,excluded=362896,r521=r521,credit=0,accepted_new=57)))
