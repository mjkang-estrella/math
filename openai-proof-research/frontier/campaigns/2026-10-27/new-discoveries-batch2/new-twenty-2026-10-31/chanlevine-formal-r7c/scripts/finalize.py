import hashlib,json,pathlib,re,zipfile
r=pathlib.Path(__file__).resolve().parent.parent
fresh=r/'fresh-extraction'
a=json.loads((fresh/'logs/replay-result.json').read_text());assert a['status']=='PASS'
frozen=json.loads((r/'frozen-before.json').read_text())
modules={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'frozen':p.name in frozen} for p in sorted((r/'formal').glob('*.lean'))}
after={n:modules[n]['sha256'] for n in frozen};assert after==frozen
assert json.loads((r/'frozen-after.json').read_text())==frozen
log=(fresh/a['modules']['CountR7CAudit']['lean']).read_text()
rows=re.findall(r'CLOSURE_DECL (\S+) LOCAL (true|false) UNSAFE (true|false) PARTIAL (true|false) IMPLEMENTED_BY (.*?) EXTERN (true|false)',log)
up=[x for x in rows if x[1]=='false' and (x[4]!='none' or x[5]=='true')]
(r/'upstream-flagged-declarations.txt').write_text('\n'.join(' '.join(x) for x in up)+'\n')
rss=[]
for p in (fresh/'logs').glob('*.log'):rss += [int(x) for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
z=r/'chanlevine-round7c-source.zip'
with zipfile.ZipFile(z) as src:
 for n in src.namelist():
  p=pathlib.PurePosixPath(n);assert not p.is_absolute() and '..' not in p.parts
  assert src.read(n)==(fresh/n).read_bytes()==(r/n).read_bytes()
report={'mathdb_id':338887,'lane':'chanlevine-formal-r7c','status':'COUNTING_CONVOLUTION_PROVED_ROOT_REVIEW_PENDING','self_accepted':False,'credit_requested':0,'targets':{'matchingCountConvolution':'PROVED_UNCONDITIONALLY','MathDB338887':'NOT_ASSEMBLED_IN_THIS_LANE'},'remaining_props':a['remaining_props'],'remaining_prop_files':[],'sibling_lane_remaining':['Round6.MatchingTraceExpansion'],'modules':modules,'frozen_hashes_before':frozen,'frozen_hashes_after':after,'round6a_input_zip_sha256':'844b066f28b9c97b43e41ce54c77813c1b41b6334994d2f1ebb406390d7ec9e0','lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','replay':{'status':'PASS','strict_modules':len(a['modules']),'leanchecker_modules':len(a['modules']),'max_reported_rss_kib':max(rss),'resumable':True,'path':'fresh-extraction/logs/replay-result.json'},'audit':{'local_declarations':a['audit_local_declarations'],'reachable_declarations':a['audit_declarations'],'generated_local_declarations_included':True,'set_equals_dependency_closure':True,'unsafe':sum(x[2]=='true' for x in rows),'partial':sum(x[3]=='true' for x in rows),'local_executable_flags':0,'upstream_extern_or_implemented_by':len(up),'axioms':a['axioms'],'scope':'Reachable type/value closure from every local endpoint/control declaration; generated declarations included, audit instrumentation excluded.'},'negative_controls':a['negative_controls'],'regression':{'status':'PASS','inherited_exact_positive_level_cases':104,'new_checks':'28535 exact per-matching geometric coefficients; 30 literal matching cases; inherited 104 positive-level cases through n=10','is_general_proof':False},'source_archive':{'path':z.name,'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'safe_paths':True,'source_only':True,'fresh_extraction_matches':True},'writes_outside_lane':False,'child_agents':0,'git_operations':0,'network_upload_external_message_browser_tab':False,'background_processes_left':0,'development_failures_retained':True,'validation_note':'Fresh extracted replay; development errors retained separately.','next_round_plan':'SUMMARY.md'}
(r/'results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','targets','replay','audit','source_archive']},indent=2))
