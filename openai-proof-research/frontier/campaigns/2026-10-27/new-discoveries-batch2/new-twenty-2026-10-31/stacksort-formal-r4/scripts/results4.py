import pathlib,json,hashlib,zipfile,re
lane=pathlib.Path(__file__).resolve().parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
inherited={s.split()[1]:s.split()[0] for s in (lane/'hashes/inherited-before.sha256').read_text().splitlines()}
assert len(inherited)==66
modules={}
for p in sorted((lane/'src').glob('*.lean')):
 key='src/'+p.name
 if key in inherited: assert sha(p.read_bytes())==inherited[key]
 modules[p.name]={'sha256':sha(p.read_bytes()),'lines':len(p.read_text().splitlines()),'inherited':key in inherited}
assert len(modules)==73
fresh=lane/'fresh-extraction'
for n in modules:
 assert (fresh/'src'/n).read_bytes()==(lane/'src'/n).read_bytes()
order=(lane/'scripts/order.txt').read_text().splitlines()
assert len(order)==len(set(order))==73
for m in order:
 for prefix in ['build-','checker-']:
  text=(fresh/'logs'/f'{prefix}{m}.log').read_text()
  assert '\nexit 0\n' in text,(prefix,m)
archive=lane/'stacksort-source4.zip'
with zipfile.ZipFile(archive) as z:
 for n in z.namelist():
  p=pathlib.PurePosixPath(n)
  assert not p.is_absolute() and '..' not in p.parts
  assert p.suffix in {'.lean','.py','.sh','.txt'}
  assert z.read(n)==(lane/n).read_bytes()
audit=json.loads((fresh/'logs/audit-summary4.json').read_text())
logs=list((lane/'logs').glob('*.log'))+list((fresh/'logs').glob('*.log'))
peaks=[int(v) for p in logs for v in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
assert max(peaks)<6291456
assert not any('RSS CAP EXCEEDED' in p.read_text() for p in logs)
r={'round':4,'mathdb_id':345545,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,'lean':'4.34.1','mathlib_packages_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','frozen_round3_archive_sha256':'f55b693345591d1cef0291d604152a98f2d50e3ec29d5e18faa4d203b19d5d00','inherited_module_count':66,'inherited_modules_byte_identical':True,'modules':modules,'closed_requested_general_obligations':[], 'completed':['unique last-common-cut / irreducible-final-block decomposition','literal tuple standardisation surjectivity','prescribed-label collision and irreducible XI/II counts','T2 maximum in last tuple words','tuple deletion collision reflection and arity shift','CommonCutCount for r=1'], 'remaining_Props':['StackSort.Round3.CommonCutCount','StackSort.Round3.MaximumFinalCount'],'remaining_Props_equivalently':['StackSort.Seeds2.AdditiveRecursion'],'endpoints':{n:'CONDITIONAL on CommonCutCount and MaximumFinalCount' for n in ['exactSeeds20_of_counts','lower130_of_counts','mathdb_345545','limit_ge','nonvacuity','subsequence_companion']},'validation':{'fresh_empty_extraction':True,'strict_serial_fresh_rebuild':True,'leanchecker_every_module_explicit_argument':True,'module_count':73,'negative_controls':'inherited modules in final closure','literal_P5_P6_kernel_regressions':'not newly completed'},'audit':audit,'archive':{'path':archive.name,'sha256':sha(archive.read_bytes()),'safe_source_only':True},'resource_limits':{'rss_KiB':6291456,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'lean_memory_MB':3500,'malloc_arena_max':2,'one_heavy_process_at_a_time':True,'watchdog_every_lean_leanchecker_python':True,'peak_recorded_RSS_KiB':max(peaks),'watchdog_kills':0},'background_jobs_remaining':False,'next_round_plan':'PROOF.md'}
r['endpoints'].update({'mathdb_345545_max':'UNCONDITIONAL_PROVED inherited result','max_companion':'UNCONDITIONAL_PROVED inherited result','commonCutCount_proved':'NOT CLOSED; absent','maximumFinalCount_proved':'NOT CLOSED; absent','additiveRecursion_proved':'NOT CLOSED; absent','exactSeeds20_proved':'NOT CLOSED; absent','lower130':'NOT CLOSED unconditionally'})
(lane/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':r['status'],'modules':len(modules),'audit_declarations':audit['declarations'],'round4_declarations':audit['local_groups']['round4']['declarations'],'archive_sha256':r['archive']['sha256'],'peak_RSS_KiB':max(peaks)},indent=2))
