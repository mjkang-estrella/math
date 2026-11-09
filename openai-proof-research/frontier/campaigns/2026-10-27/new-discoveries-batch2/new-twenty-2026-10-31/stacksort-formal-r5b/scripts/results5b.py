import pathlib,hashlib,json,re,zipfile
b=pathlib.Path(__file__).resolve().parent.parent
mods={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'inherited':not p.name.startswith('StackSortDel5')} for p in sorted((b/'src').glob('*.lean'))}
old={line.split()[1]:line.split()[0] for line in (b/'hashes/inherited-before.sha256').read_text().splitlines()}
assert len(old)==73
assert all(mods[n]['sha256']==h for n,h in old.items())
(b/'hashes/inherited-after.sha256').write_text(''.join(f'{mods[n]["sha256"]}  {n}\n' for n in old))
order=(b/'scripts/order.txt').read_text().split()
assert len(order)==80 and len(set(order))==80
for m in order:
 assert (b/'fresh-extraction/src'/f'{m}.olean').exists(),m
 for kind in ['build','checker']:
  log=(b/'logs'/f'fresh-{kind}-{m}.log').read_text()
  assert log.rstrip().endswith('exit 0'),(kind,m)
for p in (b/'src').glob('*.lean'):
 assert p.read_bytes()==(b/'fresh-extraction/src'/p.name).read_bytes()
audit=json.loads((b/'logs/audit-summary5b.json').read_text())
logs=list((b/'logs').glob('*.log'))
peaks=[];kills=0
for p in logs:
 s=p.read_text()
 peaks += [int(x) for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)]
 kills += s.count('RSS CAP EXCEEDED')
z=b/'stacksort-source5b.zip'
with zipfile.ZipFile(z) as a:
 assert all(not pathlib.PurePosixPath(n).is_absolute() and '..' not in pathlib.PurePosixPath(n).parts for n in a.namelist())
 assert not any(n.endswith(('.olean','.ilean','.c','.o')) for n in a.namelist())
r={'round':'5B','mathdb_id':345545,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,'lean':'4.34.1','mathlib_packages_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','frozen_round4_archive_sha256':'46c01f2044c67acc490c8a48f0c7a860f89ea8299233368ca81e83f93765b0da','inherited_module_count':73,'inherited_modules_byte_identical':True,'modules':mods,'completed':['literal deletion membership equivalence, including empty reduced tuple','finite child suffix fibers with cardinalities 1,2,1','inverse suffix reconstruction and oriented insertion uniqueness','deletionEquiv between all maximum-final collision pairs and reduced representations','clipping compatibility deletion literalX = deletion XI','Nat.card equality of the two deletion domains'],'remaining_Props':['StackSort.Del5.FixedMaximumDecomposition','StackSort.Del5.TaggedDeletionCount'],'target_status':{'maximumFinalCount_proved':'NOT CLOSED; absent','maximumFinalCount_of_bridges':'PROVED, conditional on the two displayed remaining Props','CommonCutCount':'NOT WORKED ON; separate lane 5A','source_reading_endpoints':'remain conditional upstream'},'validation':{'fresh_empty_extraction':True,'strict_serial_fresh_rebuild':True,'leanchecker_every_module_explicit_argument':True,'module_count':len(order),'negative_controls':'inherited modules rebuilt and checked; new unary and empty reconstruction regressions','literal_P5_P6_kernel_regressions':'not newly completed'},'audit':audit,'archive':{'path':z.name,'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'safe_source_only':True},'resource_limits':{'rss_KiB':6291456,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'lean_memory_MB':3500,'malloc_arena_max':2,'one_heavy_process_at_a_time':True,'watchdog_every_lean_leanchecker_python':True,'peak_recorded_RSS_KiB':max(peaks),'watchdog_kill_log_occurrences':kills},'background_jobs_remaining':False,'next_round_plan':'PROOF.md'}
(b/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','inherited_module_count','inherited_modules_byte_identical','validation','archive','resource_limits']},indent=2))
