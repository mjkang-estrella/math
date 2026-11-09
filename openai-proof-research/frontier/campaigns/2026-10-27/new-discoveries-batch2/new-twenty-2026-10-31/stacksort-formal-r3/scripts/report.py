import pathlib, hashlib, json, zipfile
root = pathlib.Path(__file__).resolve().parent.parent
src = root/'src'
modules = {p.name: {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(), 'lines':len(p.read_text().splitlines()), 'inherited':p.name in {x.split()[-1].split('/')[-1] for x in (root/'hashes/inherited-before.sha256').read_text().splitlines()}} for p in sorted(src.glob('*.lean'))}
before={line.split()[-1].split('/')[-1]:line.split()[0] for line in (root/'hashes/inherited-before.sha256').read_text().splitlines()}
assert len(before)==57
assert all(modules[n]['sha256']==h for n,h in before.items())
packets=[]
for d in ('r1','r2a','r2b'):
    ps={p.name:p.read_bytes() for p in (root/'packets'/d).rglob('*.lean')}
    packets.append(ps)
assert list(map(len,packets)) == [11,27,41]
common=packets[1].keys() & packets[2].keys()
assert len(common)==11 and all(packets[1][n]==packets[2][n] for n in common)
assert len(set().union(*(p.keys() for p in packets)))==57
for ps in packets:
    for n,b in ps.items(): assert (src/n).read_bytes()==b
archive=root/'stacksort-source3.zip'
with zipfile.ZipFile(archive) as z:
    for n in z.namelist():
        p=pathlib.PurePosixPath(n)
        assert not p.is_absolute() and '..' not in p.parts
        assert p.suffix in ('.lean','.sh','.txt','.py')
        assert z.read(n)==(root/n).read_bytes()
replay=root/'fresh-extraction'
order=(root/'scripts/order.txt').read_text().splitlines()
assert len(order)==len(modules)==66
for m in order:
    assert (replay/'src'/f'{m}.lean').read_bytes()==(src/f'{m}.lean').read_bytes()
    assert (replay/'src'/f'{m}.olean').exists()
    for prefix in ('build-','checker-'):
        s=(replay/'logs'/f'{prefix}{m}.log').read_text()
        assert '\nexit 0\n' in s, (prefix,m)
audit=json.loads((replay/'logs/audit-summary.json').read_text())
result={'round':3,'mathdb_id':345545,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,
'lean':'4.34.1','mathlib_packages_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'merge':{'packet_counts':[11,27,41],'shared_names':11,'union':57,'conflicts':0,'all_inherited_byte_identical':True},
'modules':modules,
'closed_obligations':['RootSplit','DoublingInjection','Doubling'],
'shuffle_core':{'finite_subset_word_standardisation':'PROVED onto literal permutation domain','word_pair_choose_count':'PROVED','arbitrary_tuple_family_tensor_count':'PROVED','prescribed_label_tensor_count':'PROVED','tuple_collision_boundary_irreducibility_invariance':'PROVED','unique_common_cut_decomposition':'OPEN','literal_tuple_standardisation_surjectivity':'NOT separately established'},
'endpoints':{'StackSort.Round3.mathdb_345545':'CONDITIONAL on StackSort.Seeds2.AdditiveRecursion','StackSort.Round3.limit_ge':'same one Prop','StackSort.Round3.nonvacuity':'same one Prop','StackSort.Round3.subsequence_companion':'same one Prop; index(130,k)+1=131*2^k','StackSort.Round3.mathdb_345545_max':'UNCONDITIONAL','StackSort.Round3.max_companion':'UNCONDITIONAL','exactSeeds20_proved':'NOT CLOSED','lower130_of_recursion':'CONDITIONAL on AdditiveRecursion'},
'remaining_Props':['StackSort.Seeds2.AdditiveRecursion'],
'remaining_Props_split_equivalently':['StackSort.Round3.CommonCutCount','StackSort.Round3.MaximumFinalCount'],
'validation':{'strict_initial_57_module_rebuild':True,'fresh_empty_extraction':True,'strict_serial_fresh_rebuild':True,'leanchecker_every_module_explicit_argument':True,'module_count':66,'negative_controls':'inherited control modules imported by StackSortFinal3','literal_P5_P6_kernel_regressions':'not completed'},
'audit':audit,
'python_diagnostics':json.loads((root/'regression.json').read_text()),
'archive':{'path':archive.name,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'safe_source_only':True},
'resource_limits':{'rss_KiB':6291456,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'lean_memory_MB':3500,'malloc_arena_max':2,'one_heavy_process_at_a_time':True,'watchdog_every_lean_leanchecker_python':True},
'background_jobs_remaining':False,
'next_round_plan':'PROOF.md'}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','merge','closed_obligations','archive')},indent=2))
