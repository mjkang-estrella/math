import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parents[1]
nodes=json.loads((P.parent/'expanded-corpus-r153/outputs/pure-dag.json').read_text())['nodes']
markers=sorted(x.stem for x in (P/'replay-r1/logs/replay').glob('*.ok'))
result={
 'mathdb_id':352253,'status':'PARTIAL_CONDITIONAL_FORMALIZATION','acceptance':False,'credit':0,
 'lean_version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'checked_endpoint':'Endpoint.conditional_negation',
 'endpoint_premises':['Endpoint.PureLowerBound','Endpoint.ChainAbsence'],
 'unconditional_checked_results':['Concrete.original_doubled_cubic','Concrete.pure_path','Concrete.seven_move_witness','Concrete.nonminimal','Controls.chain_positive','Controls.move_positive','AliasControl.contains_chain','Literal.closed_certificate_sound','RawClosure.closed_set_sound','RawClosure.indexed_extend'],
 'canonical_certificate':{'generated_entries':2328,'generated_arcs':9846,'chunks':582,'checked_chunks':108,'checked_entries':432,'checked_prefix_arcs':sum(len(n['children']) for n in nodes[:432]),'last_checked_chunk':'Closure107','full_canonical_bound_compiled':False,'counts_2328_9846_kernel_checked':False},
 'replay':{'full_strict_complete':False,'driver_successful_modules':len(markers),'total_archive_modules':len((P/'modules.txt').read_text().splitlines()),'extra_checked_module':'AuditPartial','last_driver_success':'Closure107','stop':'controlled boundary pause; no active Lean process killed','resume':'bash replay-r1/scripts/replay.sh --resume','success_markers':markers,'archive_amended_after_extraction':['Audit.lean counter annotation','AuditPartial.lean added','module and source manifests'],'checked_131_module_source_bytes_unchanged':True},
 'audit':{'partial_metadata_pass':True,'partial_local_declarations':3017,'full_metadata_pass':False,'source_scan_pass':True,'endpoint_axioms':['propext','Classical.choice','Quot.sound']},
 'remaining':['Finish canonical certificate replay and RawResult/Final/full Audit','Prove canonical-to-literal relabelling transport','Prove chain absence for Concrete.g7','Complete independent formal-fidelity review and complete strict extracted replay'],
 'resources':{'rss_kib':6291456,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_memory_mb':3500,'malloc_arena_max':2,'limits_raised':False,'replay_serialized':True,'development_nonoverlap_fully_established':False,'incidents':'logs/development-incidents.txt'},
 'restrictions':{'no_children':True,'no_network':True,'no_git':True,'no_external_messages':True,'no_discovery_scripts_executed':True,'writes_lane_only':True},
 'source_zip_sha256':hashlib.sha256((P/'source.zip').read_bytes()).hexdigest(),
 'self_acceptance':False}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print('driver_checked',len(markers),'total',result['replay']['total_archive_modules'],'prefix_arcs',result['canonical_certificate']['checked_prefix_arcs'])
