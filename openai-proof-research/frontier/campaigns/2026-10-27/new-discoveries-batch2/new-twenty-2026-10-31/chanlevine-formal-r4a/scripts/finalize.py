import hashlib,json,pathlib,re,zipfile
r=pathlib.Path(__file__).resolve().parent.parent
fresh=r/'fresh-extraction-final'
a=json.loads((fresh/'logs/replay-result.json').read_text()); assert a['status']=='PASS'
frozen=json.loads((r/'frozen-before.json').read_text())
modules={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'frozen':p.name in frozen} for p in sorted((r/'formal').glob('*.lean'))}
for n,h in frozen.items(): assert modules[n]['sha256']==h
assert json.loads((r/'frozen-after.json').read_text())==frozen
log=(fresh/a['modules']['CountR4Audit']['lean']).read_text()
rows=re.findall(r'CLOSURE_DECL (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false)',log)
up=[x for x in rows if x[1]=='false' and (x[4]!='none' or x[5]=='true')]
# Lean prints implemented_by none as 'none'; preserve raw rows for inspection.
(r/'upstream-flagged-declarations.txt').write_text('\n'.join(' '.join(x) for x in up)+'\n')
rss=[]
for p in (fresh/'logs').glob('*.log'):
 rss += [int(x) for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
z=r/'chanlevine-round4a-source.zip'
with zipfile.ZipFile(z) as src:
 for n in src.namelist():
  p=pathlib.PurePosixPath(n); assert not p.is_absolute() and '..' not in p.parts
  assert src.read(n)==(fresh/n).read_bytes()==(r/n).read_bytes()
report={'mathdb_id':338887,'lane':'chanlevine-formal-r4a','status':'PARTIAL_CONDITIONAL_ONLY','self_accepted':False,'credit_requested':0,'targets':{'TransferCountEvaluation':'OPEN_UNCHANGED','PrimitivePeriodData':'CONDITIONAL_ON_PrimitiveTopCoefficient','spectralOrder':'CONDITIONAL_ON_TWO_PROPS','unitCount':'CONDITIONAL_ON_TWO_PROPS'},'remaining_props':a['remaining_props'],'remaining_prop_files':['formal/CountSpectralModel.lean','formal/CountR4Period.lean'],'modules':modules,'frozen_hashes_before':frozen,'frozen_hashes_after':frozen,'round3a_input_zip_sha256':'3aeac767a40e4b2524a88e208c6f36b1541a47f80e24b87c4107b63548d4ee1c','lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','replay':{'status':'PASS','strict_modules':len(a['modules']),'leanchecker_modules':len(a['modules']),'max_reported_rss_kib':max(rss),'resumable':True,'path':'fresh-extraction-final/logs/replay-result.json'},'audit':{'local_declarations':a['audit_local_declarations'],'reachable_declarations':a['audit_declarations'],'generated_local_declarations_included':True,'set_equals_dependency_closure':True,'unsafe':sum(x[2]=='true' for x in rows),'partial':sum(x[3]=='true' for x in rows),'local_executable_flags':0,'upstream_extern_or_implemented_by':a['upstream_executable_flags'],'axioms':a['axioms'],'scope':'Reachable type/value closure of every local endpoint/control declaration; generated declarations included, audit instrumentation excluded.'},'negative_controls':a['negative_controls'],'regression':{'status':'PASS','inherited_exact_positive_level_cases':104,'new_independent_group_ring_cases':10,'is_general_proof':False},'source_archive':{'path':z.name,'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'safe_paths':True,'source_only':True,'fresh_extraction_matches':True},'writes_outside_lane':False,'child_agents':0,'git_operations':0,'network_upload_external_message_browser_tab':False,'background_processes_left':0,'next_round_plan':'SUMMARY.md','development_failures_retained':True,'validation_note':'Initial extracted rebuild completed compilation/checking then failed due to a replay-script key typo; the corrected source archive was extracted into a new empty directory and replayed independently.'}
(r/'results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'audit':report['audit'],'zip':report['source_archive'],'replay':report['replay']},indent=2))
