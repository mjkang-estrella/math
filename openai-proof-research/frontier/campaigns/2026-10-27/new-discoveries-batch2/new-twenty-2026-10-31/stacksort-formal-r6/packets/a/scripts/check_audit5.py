import json,sys,pathlib
p=pathlib.Path(sys.argv[1]); rows=[json.loads(x) for x in p.open()]
d={r['name']:r for r in rows if 'name' in r}; mods={r['module_record']:r for r in rows if 'module_record' in r}
closure=set();todo=['StackSortCut5Final']
while todo:
 m=todo.pop()
 if m not in closure:
  closure.add(m);todo.extend(mods[m]['imports'])
expected={n for m in closure for n in mods[m]['const_names']}
actual={n for n,r in d.items() if r['module'] in closure}
assert expected==actual
names=['commonCutCount_proved','commonCutCount_raw','glue_mem','glue_injective','glue_surjective','pieces_card','pieces_card_sum','XI_partition','labelled_split','labelled_append','correction_eq_raw']
proofs={}
for name in names:
 ep='StackSort.Cut5.'+name; seen=set();todo=[ep]
 while todo:
  n=todo.pop()
  if n not in seen:
   seen.add(n);todo.extend(d[n]['deps'])
 axs=sorted(n for n in seen if d[n]['axiom'])
 assert set(axs)<={'propext','Classical.choice','Quot.sound'},(ep,axs)
 proofs[ep]={'declarations':len(seen),'axioms':axs,'local':sum(d[n]['local'] for n in seen)}
flags=['unsafe','partial','unsafe_rec','implemented_by','extern','axiom']
local={n for n in actual if d[n]['local']}
for n in local:
 assert not any(d[n][f] for f in flags),(n,d[n])
extras={n for m in closure for n in mods[m]['compiler_extra_names']}
groups={'round5a':{n for n in local if d[n]['module'] in {'StackSortCut5Labels','StackSortCut5Pieces','StackSortCut5Count','StackSortCut5Clip','StackSortCut5Final'}},'inherited':{n for n in local if d[n]['module'] not in {'StackSortCut5Labels','StackSortCut5Pieces','StackSortCut5Count','StackSortCut5Clip','StackSortCut5Final'}}}
report={'closure_equals_audited_set':True,'declarations':len(actual),'import_modules':len(closure),'local_declarations':len(local),'upstream_declarations':len(actual-local),'compiler_extra_symbols':len(extras),'compiler_symbols_with_kernel_metadata':len(extras & set(d)),'local_metadata':{f:sum(bool(d[n][f]) for n in local) for f in flags},'upstream_metadata':{f:sum(bool(d[n][f]) for n in actual-local) for f in flags},'local_groups':{g:{'declarations':len(ns),'metadata':{f:sum(bool(d[n][f]) for n in ns) for f in flags}} for g,ns in groups.items()},'endpoints':proofs}
p.with_name('audit-summary5.json').write_text(json.dumps(report,indent=2)+'\n')
p.with_name('compiler-symbols5.json').write_text(json.dumps({'names':sorted(extras),'kernel_declarations':sorted(extras & set(d))},indent=2)+'\n')
print(json.dumps(report,indent=2))
