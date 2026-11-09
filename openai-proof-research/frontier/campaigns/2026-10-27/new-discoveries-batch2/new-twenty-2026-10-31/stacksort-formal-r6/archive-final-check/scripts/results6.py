import pathlib,json,hashlib,re
p=pathlib.Path(__file__).resolve().parent.parent
mods={f.name:{'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'lines':len(f.read_text().splitlines()),'inherited':f.stem not in {'StackSortTagged6','StackSortTaggedCount6','StackSortFixed6','StackSortFixedCount6','StackSortFinal6','StackSortAudit6'}} for f in sorted((p/'src').glob('*.lean'))}
for d in ['a','b','r4']:
 for f in (p/'packets'/d/'src').glob('*.lean'):
  assert f.read_bytes()==(p/'src'/f.name).read_bytes()
order=(p/'scripts/order.txt').read_text().split()
assert len(order)==len(mods)
assert all((p/f'fresh-extraction/src/{m}.olean').exists() for m in order)
assert all((p/f'logs/fresh-checker-{m}.ok').exists() for m in order)
audit=json.loads((p/'logs/audit-summary6.json').read_text())
peak=max([0]+[int(x) for f in (p/'logs').glob('*.log') for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',f.read_text())])
res={'round':6,'mathdb_id':345545,'status':'IMPLEMENTED_NOT_ACCEPTED','self_accepted':False,'credit':0,'lean':'4.34.1','mathlib_packages_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','inputs':{'5A':'31dfd87cce967ee5e90ce7eeb1399e0a5bbee391f9c8be5a060dcab0ce98cb7d','5B':'3ca4967368059758312d4f63080113140ca73872eecc1ad02a85846b118c6c10'},'merge':{'distinct_modules':86,'shared_modules':73,'conflicts':0,'byte_identical':True},'modules':mods,'remaining_Props':[],'endpoints':{n:'UNCONDITIONAL_PROVED' for n in ['taggedDeletionCount_proved','fixedMaximumDecomposition_proved','maximumFinalCount_proved','additiveRecursion_proved','exactSeeds20_proved','lower130','mathdb_345545','limit_ge','nonvacuity','subsequence_companion','mathdb_345545_max','max_companion']},'validation':{'fresh_extracted_strict_serial_rebuild':True,'explicit_module_leanchecker_all':True,'module_count':len(order),'negative_controls':'inherited checked modules plus scripts/regress6.py','literal_P5_P6_direct_kernel_decide':'not newly claimed; exactSeeds20_proved supplies literal equalities'},'audit':audit,'archive':{'path':'stacksort-source6.zip','sha256':hashlib.sha256((p/'stacksort-source6.zip').read_bytes()).hexdigest(),'source_only':True},'resource_limits':{'rss_KiB':6291456,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'lean_memory_MB':3500,'peak_recorded_RSS_KiB':peak,'one_heavy_process_at_a_time':True},'background_jobs_remaining':False}
(p/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ['modules','audit']},indent=2))
