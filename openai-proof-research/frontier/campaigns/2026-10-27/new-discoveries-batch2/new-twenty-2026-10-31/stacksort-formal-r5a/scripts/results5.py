import pathlib,json,hashlib,zipfile,re
lane=pathlib.Path(__file__).resolve().parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
inherited={s.split()[1]:s.split()[0] for s in (lane/'hashes/inherited-before.sha256').read_text().splitlines()}
assert len(inherited)==73
modules={}
for p in sorted((lane/'src').glob('*.lean')):
 key='src/'+p.name
 if key in inherited: assert sha(p.read_bytes())==inherited[key]
 modules[p.name]={'sha256':sha(p.read_bytes()),'lines':len(p.read_text().splitlines()),'inherited':key in inherited}
assert len(modules)==79
fresh=lane/'fresh-extraction'
for n in modules: assert (fresh/'src'/n).read_bytes()==(lane/'src'/n).read_bytes()
order=(lane/'scripts/order.txt').read_text().splitlines()
assert len(order)==len(set(order))==79
for m in order:
 for prefix in ['build-','checker-']:
  t=(fresh/'logs'/f'{prefix}{m}.log').read_text()
  assert '\nexit 0\n' in t,(prefix,m)
archive=lane/'stacksort-source5a.zip'
with zipfile.ZipFile(archive) as z:
 for n in z.namelist():
  p=pathlib.PurePosixPath(n)
  assert not p.is_absolute() and '..' not in p.parts
  assert p.suffix in {'.lean','.py','.sh','.txt'}
  assert z.read(n)==(lane/n).read_bytes(),n
audit=json.loads((fresh/'logs/audit-summary5.json').read_text())
logs=list((lane/'logs').glob('*.log'))+list((fresh/'logs').glob('*.log'))
peaks=[int(v) for p in logs for v in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
assert max(peaks)<6291456
assert not any('RSS CAP EXCEEDED' in p.read_text() for p in logs)
new={n for n,v in modules.items() if not v['inherited']}
assert all(n.startswith('StackSortCut5') for n in new)
for n in new - {'StackSortCut5Audit.lean'}:
 text=(lane/'src'/n).read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',text),n
r={'round':'5A','mathdb_id':345545,'status':'REQUESTED_LANE_TARGET_PROVED_NOT_ACCEPTED','self_accepted':False,'credit':0,
 'lean':'4.34.1','mathlib_packages_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'frozen_round4_archive_sha256':'46c01f2044c67acc490c8a48f0c7a860f89ea8299233368ca81e83f93765b0da',
 'inherited_module_count':73,'inherited_modules_byte_identical':True,'modules':modules,
 'closed_requested_general_obligations':['StackSort.Round3.CommonCutCount'],
 'endpoint':'StackSort.Cut5.commonCutCount_proved : StackSort.Round3.CommonCutCount',
 'endpoint_hypotheses':[], 'remaining_Props':['StackSort.Round3.MaximumFinalCount'],
 'endpoint_status':{'commonCutCount_proved':'UNCONDITIONAL_PROVED','commonCutCount_raw':'UNCONDITIONAL_PROVED for all M>0 and arbitrary r,s',
 'maximumFinalCount_proved':'NOT WORKED ON; parallel lane 5B','source_refutation':'inherited endpoints still require MaximumFinalCount after supplying this lane'},
 'validation':{'fresh_empty_extraction':True,'strict_serial_fresh_rebuild':True,'leanchecker_every_module_explicit_argument':True,
 'module_count':79,'negative_controls':'inherited modules retained through StackSortFinal4','literal_P5_P6_kernel_regressions':'not newly claimed'},
 'audit':audit,'archive':{'path':archive.name,'sha256':sha(archive.read_bytes()),'safe_source_only':True},
 'resource_limits':{'rss_KiB':6291456,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'lean_memory_MB':3500,'malloc_arena_max':2,
 'one_heavy_process_at_a_time':True,'watchdog_every_lean_leanchecker_python':True,'peak_recorded_RSS_KiB':max(peaks),'watchdog_kills':0},
 'background_jobs_remaining':False,'integration':'Import StackSortCut5Final and use StackSort.Cut5.commonCutCount_proved. Root decides acceptance.'}
(lane/'results.json').write_text(json.dumps(r,indent=2)+'\n')
(lane/'audit-summary.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({'status':r['status'],'modules':len(modules),'audit_declarations':audit['declarations'],
 'new_declarations':audit['local_groups']['round5a']['declarations'],'archive_sha256':r['archive']['sha256'],'peak_RSS_KiB':max(peaks)},indent=2))
