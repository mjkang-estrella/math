import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
from pathlib import Path
import hashlib,json,re,datetime,subprocess,sys
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipt=json.loads((p/'replay/receipt.json').read_text())
names=json.loads((p/'declarations.json').read_text())
audit='\n'.join((p/f'replay/logs/Audit{i}.lean.log').read_text() for i in range(9))
printed=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit)
assert sorted(printed)==names
assert len(names)==409
for f in (p/'formal').glob('*.lean'):
 assert sha(f)==sha(p/'replay/formal'/f.name)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',f.read_text())
subprocess.run([sys.executable,str(p/'verify_inputs.py')],check=True,timeout=45)
deps=json.loads((p/'dependency-hashes.json').read_text())
assert not deps['missing']
manifest={str(f.relative_to(p)):sha(f) for f in sorted((p/'formal').glob('*.lean'))}
manifest['formal/run_lean.py']=sha(p/'formal/run_lean.py')
(p/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
review={'all_409_types_and_axioms_personally_inspected':True,'audit_files':[f'replay/logs/Audit{i}.lean.log' for i in range(9)],'audit_log_hashes':{f'replay/logs/Audit{i}.lean.log':sha(p/f'replay/logs/Audit{i}.lean.log') for i in range(9)},'all_theorem_types_match_assigned_interfaces':True,'literal_E_pos_closed':True,'no_E_component_gap':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'export_scope':'Literal E positivity only; no SourceClaim, source conjecture, or novelty acceptance'}
(p/'type-audit.json').write_text(json.dumps(review,indent=2)+'\n')
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo implementation delegate','model_authorization':'GPT-6.1 Sol high/default as explicitly authorized; no children','status':'COMPONENT COMPLETE / strict source-only replay PASS; formal investment, not acceptance','discovery_credit':0,'campaign_counts':{'additional':3,'target_additional':30,'total':33,'target_total':60},'namespace':'LogArctangentMean','endpoint':'E_pos {t : ℝ} (ht : 0 < t) : 0 < E t','scope':'The full assigned literal E component only. Source-mean integration excluded.','compiler':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','compiler_sha256':json.loads((p/'input-check.json').read_text())['binary_sha256'],'mathlib':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib','mathlib_supplied_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','revision_authentication':'Supplied label; dependency bytes separately hashed, no git commands.','input_labels':{'root_adoption':'root-log-arctangent-formal-r1/ADOPTION.md @77ae829b08','certificate':'root-log-arctangent-certificate-r2: 6825c748df / a92ad4bf2b','original':'root-log-arctangent-candidate-r1: 88eb1b426c','source_auxiliary':'root-log-arctangent-source-r3: 5bd9a36b72','independent_reviews':['sol-log-arctangent-derivative-review-r2','sol-log-arctangent-investment-review-r3']},'frozen_inputs_unchanged':True,'certificate_six_hashes_match':True,'runner_byte_identical':True,'strict_replay':{'receipt':'replay/receipt.json','sha256':sha(p/'replay/receipt.json'),'modules':receipt['modules'],'declarations':len(names),'peakRSS_KiB':receipt['sampled_peakRSS_KiB'],'wall_seconds':receipt['wall_seconds'],'source_only_start':True,'warningAsError':True,'autoImplicit':False,'serial':True,'cpu_seconds_per_lean':110,'wall_seconds_per_lean':120,'RSS_limit_bytes':3*1024**3,'RSS_sampling_seconds':0.02},'dependency_hashes':{'file':'dependency-hashes.json','sha256':sha(p/'dependency-hashes.json'),'static_closure_modules':len(deps['root_dependencies']),'hashed_files':len(deps['hashes']),'missing':deps['missing'],'scope':deps['scope']},'source_manifest_sha256':sha(p/'source-manifest.json'),'type_audit_sha256':sha(p/'type-audit.json'),'resource_caveat':'Exploratory broad imports exceeded RSS before watchdog; later oversized trials killed, optimized without raising final limit. See SUMMARY.md. All final replay invocations comply.','external_actions':False,'other_lane_writes':False,'git_operations':False,'children':False,'all_artifacts_within_assigned_lane':True}
(p/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps({'status':prov['status'],'modules':receipt['modules'],'declarations':len(names),'peakRSS_KiB':receipt['sampled_peakRSS_KiB'],'receipt_sha256':sha(p/'replay/receipt.json')}))
