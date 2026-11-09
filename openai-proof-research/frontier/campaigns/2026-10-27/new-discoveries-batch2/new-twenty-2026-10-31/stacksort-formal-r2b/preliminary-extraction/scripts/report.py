import pathlib,json,hashlib,re
root=pathlib.Path(__file__).resolve().parent.parent
mods={}
for p in sorted(list((root/'frozen').glob('*.lean'))+list(root.glob('StackSortSeeds2*.lean'))):
    data=p.read_bytes();mods[str(p.relative_to(root))]={'sha256':hashlib.sha256(data).hexdigest(),'lines':len(data.splitlines())}
expected={pathlib.Path(line.split()[-1]).name:line.split()[0] for line in (root/'hashes/frozen-before.sha256').read_text().splitlines()}
assert len(expected)==11
assert all(mods['frozen/'+n]['sha256']==h for n,h in expected.items())
new=[p.stem for p in root.glob('StackSortSeeds2*.lean')]
allmods=list(expected)
logs={}
for name in new+[pathlib.Path(p).stem for p in allmods]:
    for kind in ['build','checker']:
        p=root/'logs'/f'{kind}-{name}.txt'
        assert p.exists() and p.read_text().endswith('exit 0\n'),str(p)
        logs[f'{kind}-{name}']=str(p.relative_to(root))
audit=json.loads((root/'audit-summary.json').read_text())
assert audit['closure_equals_audited_set']
peak=0
for p in (root/'logs').glob('*.log'):
    t=p.read_text()
    assert '\nRSS CAP EXCEEDED ' not in t
    for n in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',t):peak=max(peak,int(n))
r={'mathdb_id':345545,'lane':'ROUND_2B_EXACT_SEEDS','status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'credit':0,
'lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'frozen_source_packet_sha256':'67a3893f3a08616fe9d4480ce28b166cbf410df5d9edf4ca5ccb054340253dde',
'frozen_modules_byte_identical':True,'modules':mods,
'endpoints':{'exactSeeds20_proved':'NOT CLOSED; absent','exactSeeds20_of_additiveRecursion':'PROVED conditional on StackSort.Seeds2.AdditiveRecursion','exactSeeds4':'UNCONDITIONAL_PROVED','table_recursion':'UNCONDITIONAL_PROVED; arithmetic table, not count identification','irreducible_maximum_last':'UNCONDITIONAL_PROVED (T2)'},
'remaining_Props':['StackSort.Seeds2.AdditiveRecursion'],
'completed':['literal tuple domain and XI_one','word-level root splitting equivalence and 1,2,1 alternatives','irreducible maximum final output position','top-max recursion uniqueness','kernel row certificates through 20','conditional exact seeds endpoint'],
'not_claimed':['T1 common-cut shuffle factorization','counted tuple maximum deletion identity','unconditional ExactSeeds20','literal P5 or P6 kernel regressions','DoublingInjection','RootSplit','lower130 linkage'],
'python_diagnostics':{'topmax_cached_agreement_through':20,'independent_literal_enumeration_through':8,'is_combinatorial_proof':False},
'audit':audit,'validation':{'strict_build_and_explicit_module_checkers':True,'logs':logs},
'resource_compliance':True,'peak_recorded_single_command_rss_KiB':peak,
'resource_incidents':['whole-row 11 reduction hit -M3500 interpreter limit, below RSS cap; resolved by splitting proofs'],
'audit_corrections':['sections compiler companion detected and removed by explicit Nat.rec'],
'background_jobs_remaining':False,'source_archive':'stacksort-seeds2-source.zip',
'source_archive_sha256_file':'stacksort-seeds2-source.zip.sha256','next_round_plan':'PROOF.md'}
(root/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print('Reported',len(mods),'modules; exact frozen hashes and successful build/checker logs verified.')
