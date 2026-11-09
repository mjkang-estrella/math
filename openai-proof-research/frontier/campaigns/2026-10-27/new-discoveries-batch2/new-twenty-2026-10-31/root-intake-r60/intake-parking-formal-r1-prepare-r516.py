"""Root documentary verification of 323531 formal r1, kernel-failure evidence and the r516 metadata packet; no root mathematics or Lean execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'parking-strong-a2-formal-sol-r1';assert not (P/'expanded-corpus-r516').exists()

# Every documentary check precedes any root mutation.
fex=manifest(F,'OWN-MANIFEST.json',270,'terminal_seal_85','terminal_noncircular_self_exclusions');frozen(F,36)
assert sha(F/'TASK.txt')==read(ROOT/'parking-strong-a2-formal-r1-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['base_compile_07','base_checker_08','base_compile_public_11','base_lowstack_compile_18','base_small_lean_stack_20','scalar_checker_21','base_compile_eval_23','base_span_compile_26','scalar_commonzero_compile_27','scalar_directions_compile_30','base_kernel_32','base_parametric_kernel_39','scalar_light_compile_41','base_small_kernel_46','quotient_kernel_50','count_compile_52','count_repaired_compile_55','count_card_rw_compile_57','count_sprod_compile_61','count_normal_compile_63','count_kernel_66','count_nohundred_compile_70','count_endpoint_kernel_73','negative_expected_failure_76']}
failures['scalar_compile_15.receipt.json']=250;failures['scalar_kernel_full_34.receipt.json']=250
frec=receipts(F,failures);assert read(F/'terminal_seal_85.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/323531.json')
assert result['status']=='INCOMPLETE_UNCREDITED_HANDOFF' and result['credit']==0 and result['scientific_status']=='HOLD' and result['literal_endpoint'] is False and result['full_parking_polymorphic_checkpoint'] is False
def last(label):
 rows=[json.loads(x) for x in (F/(label+'.output.txt')).read_text(errors='replace').splitlines() if x.startswith('{')];return rows[-1]
trio={'propext','Classical.choice','Quot.sound'}
def axioms_ok(label):
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',(F/(label+'.output.txt')).read_text(errors='replace'));assert found,label
 assert all({y.strip() for y in f.split(',')}<=trio for f in found),label
 return len(found)
def compile_row(module,label):
 c=last(label);assert c['mode']=='compile' and c['module']==module and c['exit']==0 and read(F/(label+'.receipt.json'))['exit']==0
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and c['source_sha256']==sha(F/'src'/(module+'.lean')) and c['olean_sha256']==sha(F/'build'/(module+'.olean'))
 return c
assert set(result['strict_green_modules'])=={'ParkingScalar','ParkingSymmetry','ParkingPositive'}
green=[]
for module,v in result['strict_green_modules'].items():
 c=compile_row(module,v['compile']);k=last(v['kernel']);assert k['mode']=='check' and k['module']==module and k['exit']==0 and k['argv']==[pins['leanchecker_bin'],module] and k['source_sha256']==c['source_sha256'] and k['olean_sha256']==c['olean_sha256'] and read(F/(v['kernel']+'.receipt.json'))['exit']==0
 green.append(dict(module=module,source_sha256=c['source_sha256'],olean_sha256=c['olean_sha256'],compile=v['compile'],checker=v['kernel'],compile_receipt_sha256=sha(F/(v['compile']+'.receipt.json')),checker_receipt_sha256=sha(F/(v['kernel']+'.receipt.json'))))
compiled_only=[]
for module,cl,kl in [('ParkingBase','base_no_quotient_compile_44','base_small_kernel_46'),('ParkingQuotient','quotient_compile_47','quotient_kernel_50'),('ParkingCount','count_nohundred_strict_72','count_endpoint_kernel_73')]:
 c=compile_row(module,cl);k=last(kl);assert k['exit']==1 and k['source_sha256']==c['source_sha256'] and k['olean_sha256']==c['olean_sha256'] and 'failed to read file' in (F/(kl+'.output.txt')).read_text(errors='replace')
 compiled_only.append(dict(module=module,compile=cl,failed_checker=kl))
assert axioms_ok('count_nohundred_strict_72')>0 and axioms_ok('scalar_exposed_compile_54')>0
assert read(F/'negative_expected_failure_76.receipt.json')['exit']==1 and (F/'tools/low_stack_formal.py').is_file()
for q in (F/'src').glob('*.lean'):assert not re.search(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|^\s*axiom\b',q.read_text(),re.M),q.name

evidence=[]
for lane in ['high-girth-ur-matching-formal-sol-r4','high-girth-ur-matching-formal-sol-r5','parking-strong-a2-formal-sol-r1']:
 for q in sorted((P/lane).glob('*.output.txt')):
  text=q.read_text(errors='replace');m=re.search(r"failed to read file '([^']+)'",text)
  if m:
   rec=read(q.with_name(q.name[:-len('.output.txt')]+'.receipt.json'));evidence.append(dict(lane=lane,label=q.name[:-len('.output.txt')],file=m.group(1).split('/lean/')[-1],exit=rec['exit'],wall_s=rec.get('wall_s'),sampled_group_rss_peak_bytes=rec.get('sampled_group_rss_peak_bytes'),as_limit_bytes=rec.get('as_limit_bytes')))
assert evidence and all(x['as_limit_bytes']==6*1024**3 for x in evidence)
save(ROOT/'kernel-read-failure-evidence.json',dict(utc=now,count=len(evidence),distinct_files=sorted({x['file'] for x in evidence}),max_sampled_rss_bytes=max(x['sampled_group_rss_peak_bytes'] for x in evidence),rows=evidence,root_hypothesis='leanchecker memory-maps every olean in the import closure, so RLIMIT_AS of 6 GiB may be exhausted by virtual mappings while real memory stays near 1 GiB. Inference from logs only: the failing file varies, failures occur in about one second, sampled RSS is far below the cap, and only smaller import graphs have succeeded. Not directly tested; root runs no Lean and raising the cap needs user authorization.',root_Lean_execution=False))

fs='323531 uncredited formal r1 INCOMPLETE, no literal negation, no polymorphic reflection-conjecture checkpoint, no paper. Three strict compile plus kernel green modules verified byte/log/receipt: ParkingScalar (degree-10 scaling, common zero implication, directional factorization, fixed-direction partition, ratio-line ninth-root conditions), ParkingSymmetry (swap and rotation generator identities, linear independence of the two polynomial functions, not an all-W representation bridge) and ParkingPositive (controls). ParkingCount (coordinate candidate set of size at most 46 containing every coordinate fixed point, no bijection with Fin 100, arbitrary-predicate coordinate conjunction failure), ParkingBase and ParkingQuotient strictly compile but their separate kernel checks exit 1 with failed to read file on upstream oleans, so they are NOT certified. Negative denominator control failed as intended; scalar-fragment source-only replay only. Unpaid: genuine real irreducible A2 and h=3, complexification and coordinate duality, carrying V* and all-W equivariance, the general reflection-group model and universal conjunction, multiplicity, both parking actions and identifications, kernel completion, audits, full replay, paper, independent review and root adjudication. Process disclosures: the lane used its own hash-pinned tools/low_stack_formal.py with added -s8192 and a 1 MiB stack rlimit instead of the supplied check.sh and checker.sh, keeping every CPU, AS, RSS and deadline cap and leaving helpers untouched; noncrossing definitions on pp12-13 were read after first source authoring. Root records a resource hypothesis, not a finding: the unreadable-olean kernel failures may be RLIMIT_AS exhaustion by import mapping; see root-intake-r60/kernel-read-failure-evidence.json. 270 manifest files, 36 frozen bindings verified; no root Lean execution. Scientific HOLD and credit 0 unchanged, 57/60.'
fr=dict(utc=now,mathdb_id=323531,source_lane=str(F),manifest_sha256=sha(F/'OWN-MANIFEST.json'),verified_manifest_files=270,verified_frozen_bindings=36,green_modules=green,compiled_not_kernel_green=compiled_only,runner_receipts=frec,result=result,lane_driver_sha256=sha(F/'tools/low_stack_formal.py'),scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_PAUSED_PENDING_USER_RESOURCE_DECISION',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
den=read(ROOT/'inherited-denials-r533.json');den['utc']=now;den['root_parking323531_formal_r1_scope']=fs
save(P/'parking-strong-a2-formal-parent-integration-r1.json',fr);denpath=ROOT/'inherited-denials-r534.json';save(denpath,den)
save(ROOT/'parking-formal-r1-intake-report.json',dict(utc=now,files=270,frozen=36,verified_green_modules=green,compiled_only=compiled_only,kernel_read_failures_across_lanes=len(evidence),credit=0,accepted_new=57,no_root_mathematics=True))

base=read(ROOT/'r515-config.json');active=['high-girth-ur-matching-formal-sol-r6','digraph-aalpha-minimum-source-review-sol-r1']
base.update(number=516,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{515}),peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r6.json','selection-routing-digraph-aalpha-minimum-review-r1.json','selection-routing-parking-strong-a2-formal-r1.json'],denials=str(denpath))
base['excluded_ids']=sorted(set(base['excluded_ids'])|{350767});base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/2105.10903'})
for name in ['high-girth-ur-matching-formal-parent-integration-r5.json','parking-strong-a2-review-parent-integration-r1.json','parking-strong-a2-formal-parent-integration-r1.json','expanded-corpus-r515-parent-integration.json']:base['steering']+='\n'+read(P/name)['scientific_summary']
base['steering']+='\nRoot continues uncredited 338806 formal research r6, not a scientific PASS, acceptance or source waiver; all formal bodies and flat metadata are protected from discovery. 350767 is in active independent review and entirely protected. 323531 stays under scientific HOLD with its formal lane paused. The entire works 1504.06869 with its 2017 final and 2105.10903 with its Operators and Matrices final are closed to all new deliveries including query, metadata, hosts, versions, cache, mirror, DOI, API and indirect recovery. Distinct papers are not blanket denied. 57/60 unchanged.\n'
save(ROOT/'r516-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r516=module.prepare(base)
for name in read(Path(r516['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r516['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'parking-formal-r1-r516-next-routing.json',dict(utc=now,paused_formal=dict(mathdb_id=323531,reason='Kernel checks of import-heavy modules fail under the current address-space cap; user decision requested.'),discovery=r516,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(parking_manifest=270,frozen=36,green=[x['module'] for x in green],compiled_only=[x['module'] for x in compiled_only],kernel_read_failures=len(evidence),distinct_files=len({x['file'] for x in evidence}),r516=r516,credit=0,accepted_new=57)))
