import json,sys,pathlib,collections
p=pathlib.Path(sys.argv[1]);rows=[json.loads(x) for x in p.open()]
d={r['name']:r for r in rows if 'name'in r};mods={r['module_record']:r for r in rows if 'module_record'in r}
# Exact import closure of the final module (rather than extra audit-tool imports).
closure=set();todo=['StackSortFinal3']
while todo:
 m=todo.pop()
 if m in closure:continue
 closure.add(m);todo.extend(mods[m]['imports'])
expected=set()
for m in closure:
 expected.update(mods[m]['const_names'])
actual={n for n,r in d.items() if r['module'] in closure}
assert expected==actual, {'missing':sorted(expected-actual)[:20], 'extra':sorted(actual-expected)[:20]}
allowed={'propext','Classical.choice','Quot.sound'}
endpoints=['StackSort.Round3.mathdb_345545','StackSort.Round3.limit_ge','StackSort.Round3.nonvacuity','StackSort.mathdb_345545_max','StackSort.max_companion']
endpoints += ['StackSort.Round3.subsequence_companion','StackSort.Round3.doublingInjection_proved','StackSort.Round3.rootSplit_proved','StackSort.Shuffle3.shuffleDomain_card','StackSort.Shuffle3.tupleShuffle_card','StackSort.Shuffle3.fixedTupleShuffle_card']
endpoints += ['StackSort.Round3.mathdb_345545_max','StackSort.Round3.max_companion','StackSort.Round3.exactSeeds20_of_recursion','StackSort.Round3.lower130_of_recursion','StackSort.Round3.counts_iff_additiveRecursion']
proofs={}
for ep in endpoints:
 seen=set();todo=[ep]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(d[n]['deps'])
 axs=sorted(n for n in seen if d[n]['axiom'])
 assert set(axs)<=allowed,(ep,axs)
 proofs[ep]={'declarations':len(seen),'axioms':axs,'local':sum(d[n]['local'] for n in seen)}
flags=['unsafe','partial','unsafe_rec','implemented_by','extern','axiom']
local={n for n in actual if d[n]['local']}
for n in local:
 assert not any(d[n][flag] for flag in flags),(n,d[n])
extras={n for m in closure for n in mods[m]['compiler_extra_names']}
p.with_name('compiler-symbols.json').write_text(json.dumps({'names':sorted(extras),'kernel_declarations':sorted(extras & set(d))},indent=2)+'\n')
report={'compiler_extra_symbols':len(extras),'compiler_symbols_with_kernel_metadata':len(extras & set(d)),'closure_equals_audited_set':True,'import_modules':len(closure),'declarations':len(actual),'local_declarations':len(local),'upstream_declarations':len(actual-local),'local_metadata':{f:sum(bool(d[n][f]) for n in local) for f in flags},'upstream_metadata':{f:sum(bool(d[n][f]) for n in actual-local) for f in flags},'endpoints':proofs}
report['local_groups']={label: {'declarations':len(group), 'metadata':{f:sum(bool(d[n][f]) for n in group) for f in flags}} for label,group in [('round2a',{n for n in local if d[n]['module'].startswith('StackSortInj2')}),('round2b',{n for n in local if d[n]['module'].startswith('StackSortSeeds2')}),('round3',{n for n in local if d[n]['module'] in {'StackSortShuffle3Labels','StackSortShuffle3Core','StackSortShuffle3Root','StackSortShuffle3Tuples','StackSortRootSplit3','StackSortDoubling3','StackSortSeeds3','StackSortFinal3'}}),('frozen_round1',{n for n in local if d[n]['module'] in {'StackSortBasic','StackSortMap','StackSortSplit','StackSortEquivariance','StackSortAnalysis','StackSortMaximum','StackSortCertificate','StackSortControls','StackSortSmall','StackSortFinal'}})]}
p.with_name('audit-summary.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
