import json, hashlib, zipfile
from pathlib import Path
lane=Path.cwd()
old=lane.parent/'delta-formal-r1/source.zip'
new=lane/'source.zip'
assert hashlib.sha256(old.read_bytes()).hexdigest()=='125baa73963781320fae3c287b7b87536e59908531d2c4dfa94bcf6117c7d198'
with zipfile.ZipFile(old) as a, zipfile.ZipFile(new) as b:
 names=[n for n in a.namelist() if n.startswith('lean/') and n.endswith('.lean')]
 assert len(names)==609
 assert all(a.read(n)==b.read(n) for n in names)
 assert len([n for n in b.namelist() if n.endswith('.lean')])==634
 assert not any(n.endswith(('.olean','.ilean','.so','.o')) for n in b.namelist())
mods=(lane/'replay-r2/modules.txt').read_text().splitlines()
prefix=(lane/'replay-r2/round2-prefix.txt').read_text().splitlines()
ok={p.stem for p in (lane/'replay-r2/logs/replay').glob('*.ok')}
assert len(prefix)==46 and set(prefix)<=ok
assert all(f'Closure{n:03}' in ok for n in range(108,160))
assert all(f'Closure{n:03}' not in ok for n in range(108))
assert len(ok)==98
r={
'mathdb_id':352253,'round':2,'status':'PARTIAL_SINGLE_CANONICAL_PREMISE',
'acceptance':False,'self_acceptance':False,'credit':0,
'lean_version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'checked_endpoint':'Round2.conditional_negation',
'endpoint_premises':['Round2.CanonicalLowerBound'],
'new_closed_results':['Transport.canonical_transport','ChainPrefix.no_chain','Round2.literal_lower_bound'],
'unconditional_endpoint_source':'Round2.literal_negation',
'unconditional_endpoint_checked':False,
'original_lean_files_byte_identical':609,'total_archive_modules':634,
'source_zip_sha256':hashlib.sha256(new.read_bytes()).hexdigest(),
'base_source_zip_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),
'canonical_certificate':{'generated_entries':2328,'generated_arcs':9846,'chunks':582,
'combined_checked_chunks':160,'combined_checked_entries':640,'combined_checked_prefix_arcs':955,
'last_checked_chunk':'Closure159','round2_new_checked_chunks':52,'round2_checked_interval':[108,159],
'inherited_round1_checked_interval':[0,107],
'full_canonical_bound_compiled':False,'full_census_kernel_checked':False,
'remaining_closure_interval':[160,581]},
'replay':{'full_strict_complete':False,'fresh_extracted_proof_prefix_complete':True,
'fresh_extracted_proof_prefix_modules':46,'round2_driver_successful_modules':98,
'certificate_checks_used_inherited_prefix_dependencies':True,
'inherited_closure_oleans_have_no_round2_success_markers':True,
'fresh_prefix_log':'logs/prefix-replay.log',
'certificate_logs':['logs/certificate-replay.log','logs/certificate-replay-132-159.log'],
'resume_full':'bash replay-r2/scripts/replay.sh --resume',
'resume_certificate_only':'bash replay-r2/scripts/replay-certificate.sh 160 581'},
'audit':{'partial_metadata_pass':True,'partial_local_declarations':505,
'full_metadata_pass':False,'source_scan_pass':True,
'endpoint_axioms':['propext','Classical.choice','Quot.sound'],
'partial_audit_module':'Round2AuditPartial'},
'remaining':['Closure160–Closure581','RawResult','Final','Audit','Round2Final','Round2Audit',
'Complete strict replay of all 634 modules, including rebuilding inherited Closure000–Closure107',
'Independent formal fidelity and acceptance review by root'],
'resources':{'rss_kib':6291456,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,
'lean_memory_mb':3500,'malloc_arena_max':2,'limits_raised':False,
'fresh_replay_serialized':True,'development_nonoverlap_fully_established':False,
'incidents':'logs/development-incidents.txt','background_jobs_at_handback':False},
'restrictions':{'no_children':True,'no_network':True,'no_git':True,'no_external_messages':True,
'no_discovery_scripts_executed':True,'writes_lane_only':True}}
(lane/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('Verified 609 original Lean source bytes, 634 source-only modules, 46 fresh prefix receipts, and 52 new closure receipts.')
