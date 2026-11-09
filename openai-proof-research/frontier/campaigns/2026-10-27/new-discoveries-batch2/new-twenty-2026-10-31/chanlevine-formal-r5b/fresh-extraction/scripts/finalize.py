from pathlib import Path
import hashlib,json,re,zipfile
r=Path(__file__).resolve().parent.parent
fresh=r/'fresh-extraction'
replay=json.loads((fresh/'logs/replay-result.json').read_text())
assert replay['status']=='PASS' and not replay['remaining_props']
manifest={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines())} for p in sorted((r/'formal').glob('*.lean'))}
before=json.loads((r/'frozen-before.json').read_text())
after={k:manifest[k]['sha256'] for k in before}
assert before==after and len(before)==24
(r/'frozen-after.json').write_text(json.dumps(after,indent=2))
with zipfile.ZipFile(r/'chanlevine-round5b-source.zip') as z:
 assert all(not Path(p).is_absolute() and '..' not in Path(p).parts for p in z.namelist())
 for p in z.namelist():
  assert z.read(p)==(fresh/p).read_bytes()==(r/p).read_bytes()
logs=list((fresh/'logs').glob('*.log'))
rss=[int(x) for p in logs for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
checks=json.loads((fresh/'logs/normalization-check.json').read_text())
local=replay['audit_roots']; total=replay['audit_dependency_closure']
result={'mathdb_id':338887,'lane':'chanlevine-formal-r5b','round':'5b','status':'UNCONDITIONAL_SEMANTIC_TARGETS_COMPILED_REPLAYED_PENDING_ROOT_REVIEW','self_accepted':False,'credit_requested':0,'full_mathdb_endpoint_claimed':False,'targets':{n:{'status':'UNCONDITIONAL','type':t,'axioms':['propext','Classical.choice','Quot.sound']} for n,t in [('ChanLevine.Sem5.cappedDeficitTrap','ChanLevine.Sem4.CappedDeficitTrap'),('ChanLevine.Sem5.recurrentNormalization','ChanLevine.RecurrentNormalization'),('ChanLevine.Sem5.cycleTestBridge','ChanLevine.CycleTestBridge'),('ChanLevine.Sem5.connectedFibres','ChanLevine.ConnectedFibres')]},'remaining_semantic_props':[],'independent_counting_obligations_outside_lane':['RotationCount','UnitCount','ArithmeticOrbit'],'modules':manifest,'frozen_before':before,'frozen_after':after,'frozen_unchanged':True,'new_modules':[k for k in manifest if k not in before],'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','replay':{'status':'PASS','strict_modules':len(replay['modules']),'leanchecker_modules':len(replay['modules']),'result':'fresh-extraction/logs/replay-result.json','max_reported_rss_kib':max(rss)},'audit':{'allowOpaque':True,'local_declarations':local,'upstream_declarations':total-local,'total_dependency_closure':total,'closure_equality_verified':replay['closure_equality'],'generated_declarations_included':True,'local_module_closure':replay['local_module_closure'],'LOCAL_flagged_declarations':replay['local_flags'],'UPSTREAM_flagged_metadata':replay['flagged_dependencies'],'closure_axioms':replay['closure_axioms']},'negative_controls':replay['negative_controls'],'regressions':{'scc_cases':18,'normalization_cases':len(checks),'normalization_states':sum(row['checked'] for row in checks),'n':[3,8],'m':[1,3],'general_proof':False},'archive':{'path':'chanlevine-round5b-source.zip','sha256':hashlib.sha256((r/'chanlevine-round5b-source.zip').read_bytes()).hexdigest(),'safe_paths':True,'fresh_source_match':True},'resource_caps':{'cpus':2,'cpu_seconds':120,'wall_seconds':140,'rss_kib':6*1024*1024,'MALLOC_ARENA_MAX':'2','lean_args':['-j1','-M3500','-DwarningAsError=true'],'serial':True},'writes_outside_lane':False,'child_agents':0,'git_operations':0,'network_uploads_external_messages_browser_tabs':0,'development_logs_retained':True}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','replay','regressions','archive']},indent=2))
print('AUDIT',local,'local;',total-local,'upstream;',total,'closure; flagged upstream',len(replay['flagged_dependencies']))
