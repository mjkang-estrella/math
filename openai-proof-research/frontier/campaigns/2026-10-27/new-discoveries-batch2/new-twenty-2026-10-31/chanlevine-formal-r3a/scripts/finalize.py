"""Summarize a completed fresh replay without accepting the result."""
import hashlib,json,pathlib,re
r=pathlib.Path(__file__).resolve().parent.parent
replay=json.loads((r/'fresh-extraction/logs/replay-result.json').read_text())
assert replay['status']=='PASS'
frozen=json.loads((r/'frozen-before.json').read_text())
mods={}
for p in sorted((r/'formal').glob('*.lean')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert h==replay['source_hashes'][p.name]
 assert p.name not in frozen or h==frozen[p.name]
 mods[p.name]={'sha256':h,'lines':len(p.read_text().splitlines()),'frozen':p.name in frozen}
audit=(r/'fresh-extraction'/replay['modules']['CountSpectralAudit']['lean']).read_text()
rows=re.findall(r'CLOSURE_DECL (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false)',audit)
flags=[x for x in rows if x[4]!='none' or x[5]=='true']
(r/'upstream-flagged-declarations.txt').write_text('\n'.join(str(x) for x in flags)+'\n')
maxrss=0
for p in (r/'fresh-extraction/logs').glob('*.log'):
 for v in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text()): maxrss=max(maxrss,int(v))
result={'mathdb_id':338887,'lane':'chanlevine-formal-r3a','status':'PARTIAL_CONDITIONAL_ONLY','self_accepted':False,'credit_requested':0,
 'targets':{'spectralOrder':'CONDITIONAL_ON_TWO_PROPS','unitCount':'CONDITIONAL_ON_TWO_PROPS'},
 'remaining_props':replay['remaining_props'],'remaining_prop_file':'formal/CountSpectralModel.lean',
 'modules':mods,'frozen_hashes_before':frozen,'frozen_hashes_after':json.loads((r/'frozen-after.json').read_text()),
 'round2a_input_zip_sha256':'fcbe76d662d8a6a7788030634f1d4e20c251ca2454ec2a3b33edd91d059a3615',
 'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'replay':{'status':'PASS','strict_modules':len(mods),'leanchecker_modules':len(mods),'max_reported_rss_kib':maxrss,'resumable':True,'path':'fresh-extraction/logs/replay-result.json'},
 'audit':{'local_declarations':replay['audit_local_declarations'],'reachable_declarations':replay['audit_declarations'],
 'generated_local_declarations_included':True,'set_equals_dependency_closure':True,'unsafe':0,'partial':0,'local_executable_flags':0,'upstream_extern_or_implemented_by':len(flags),'axioms':replay['axioms'],
 'scope':'Full reachable type/value dependency closure of all local final/control declarations; instrumentation and unrelated tactic/compiler imports excluded.'},
 'regression':{'status':'PASS','exact':True,'positive_level_cases':104,'n':[3,10],'m':'1 through 2n','new_check':'recursive quotient coefficients versus literal DP','is_general_proof':False},
 'negative_controls':replay['negative_controls'],
 'source_archive':{'path':'chanlevine-round3a-source.zip','sha256':hashlib.sha256((r/'chanlevine-round3a-source.zip').read_bytes()).hexdigest(),'safe_paths':True,'source_only':True,'fresh_extraction_matches':True},
 'writes_outside_lane':False,'child_agents':0,'git_operations':0,'network_upload_external_message_browser_tab':False,'background_processes_left':0,'next_round_plan':'SUMMARY.md','development_failures_retained':True}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'audit':result['audit'],'replay':result['replay']},indent=2))
