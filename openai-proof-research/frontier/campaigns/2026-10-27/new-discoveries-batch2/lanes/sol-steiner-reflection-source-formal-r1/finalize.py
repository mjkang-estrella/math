import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,datetime,signal
from pathlib import Path
signal.alarm(45)
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((R/'verification-fresh/replay-receipt.json').read_text())
assert r['status']=='PASS' and r['declaration_count']==118
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'FULL_CONCRETE_SOURCE_ENDPOINT_AND_FRESH_REPLAY_PASS_NOT_ACCEPTANCE',
 'credit':0,'counts_unchanged':{'additional':5,'total':35},
 'endpoint':'SteinerReflection.concrete_negative_H_pair',
 'refutation':'SteinerReflection.source_refutation',
 'minimum_semantics_endpoint':'SteinerReflection.source_minimum_attained',
 'unproved_mathematical_bridges':[],
 'formal_scope':'K1,29, order4, genuine connected-subgraph edge minimum and literal first-free-index last-slot reflection; negative real H-pair; sufficient counterexample to universal source question',
 'not_claimed':['acceptance','novelty/priority certification','minimal n','failure at each even order','determinant-sign refutation','negative-quartic-only inference','general all-n Steiner formal library','paper'],
 'replay':{'receipt':'verification-fresh/replay-receipt.json','receipt_sha256':sha(R/'verification-fresh/replay-receipt.json'),'declarations':118,'mathematical_modules':6,'axioms':r['axiom_union'],'all_actual_unsafe_partial_axiom_flags_false':True,'peak_group_rss_kib':max(s['peak_group_rss_kib'] for s in r['steps']),'cpu_seconds_cap':210,'wall_seconds_cap':230,'rss_cap_mib':2800,'sampling_target_seconds':.045},
 'artifacts':{n:sha(R/n) for n in ['steiner-source-component.zip','manifest.json','pins.json','provenance.json','SUMMARY.md','REPRODUCE.md']},
 'development_failure':{'stage':'initial Algebra import Mathlib.Tactic','guard_action':'killed','observed_peak_group_rss_kib':2888552,'threshold_kib':2867200,'resolution':'selective imports; no cap increase','original_log_retained':False},
 'remaining_gates':['root adjudication','independent final formal/source/prior review','publication-version limitation','any requested manuscript'],
 'strongest_objection':'Elementary star two-orbit construction/ancillary question; formalization does not establish substantive novelty.',
 'reproduction':'python replay.py steiner-source-component.zip verification-fresh-2',
 'conduct':{'solo':True,'writes_only_assigned_lane':True,'git_commands':False,'external_access_this_lane':False,'posting_contact_browser_accounts':False}}
(R/'FINAL-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
files=sorted(p for p in R.rglob('*') if p.is_file() and 'verification-fresh' not in p.parts and p.suffix not in ['.olean','.ilean'] and p.name!='manifest.sha256')
(R/'manifest.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(R))+'\n' for p in files))
print(json.dumps({'status':result['status'],'archive':result['artifacts']['steiner-source-component.zip'],'receipt':result['replay']['receipt_sha256'],'peak_mib':result['replay']['peak_group_rss_kib']/1024},indent=2))
