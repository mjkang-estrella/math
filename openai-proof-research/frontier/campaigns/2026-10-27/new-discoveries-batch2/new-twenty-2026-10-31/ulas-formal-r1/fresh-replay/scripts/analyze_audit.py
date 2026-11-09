import json,sys,collections,glob
path,out=sys.argv[1:]
rows={}; mods={}
for line in (line for f in glob.glob(path) for line in open(f)):
 r=json.loads(line)
 if 'module_record' in r: mods[r['module_record']]=r
 else:
  assert r['name'] not in rows
  rows[r['name']]=r
closure=set(); todo=['UlasFinal','UlasChecks']
while todo:
 m=todo.pop()
 if m in closure: continue
 closure.add(m); todo.extend(mods[m]['imports'])
expected=set().union(*(set(mods[m]['const_names']) for m in closure))
actual={n for n,r in rows.items() if r['module'] in closure}
assert expected==actual,(len(expected-actual),len(actual-expected))
# Compute every declaration's transitive axiom set without recursive Python frames.
axs={}
for root in actual:
 stack=[(root,False)]; visiting=set()
 while stack:
  n,finish=stack.pop()
  if n in axs: continue
  r=rows[n]
  if finish:
   aset={n} if r['axiom'] else set()
   for d in r['deps']: aset.update(axs.get(d,set()))
   axs[n]=aset; visiting.discard(n)
  else:
   if n in visiting: continue
   visiting.add(n); stack.append((n,True))
   for d in r['deps']:
    assert d in rows,(n,d)
    if d not in axs and d not in visiting: stack.append((d,False))
# Close cycles (inductives and mutual recursion) to a least fixed point.
changed=True
while changed:
 changed=False
 for n in list(axs):
  old=len(axs[n])
  for d in rows[n]['deps']: axs[n].update(axs[d])
  changed |= len(axs[n])!=old
allowed={'propext','Classical.choice','Quot.sound'}
local=[r for n,r in rows.items() if n in actual and r['local']]
for r in local:
 assert not any(r[k] for k in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern'])
 assert axs[r['name']]<=allowed,(r['name'],axs[r['name']])
def counts(rs):
 return dict(declarations=len(rs),**{k:sum(bool(r[k]) for r in rs) for k in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']})
result=dict(audited_equals_import_closure=True,expected_declarations=len(expected),audited_declarations=len(actual),modules=len(closure),LOCAL=counts(local),upstream=counts([rows[n] for n in actual if not rows[n]['local']]),endpoint_axioms={n:sorted(axs[n]) for n in ['Ulas.full_theorem','Ulas.mathdb_342364','Ulas.conj61_some']},local_axioms={r['name']:sorted(axs[r['name']]) for r in local},upstream_axioms=sorted(set().union(*(axs[n] for n in actual if not rows[n]['local']))))
json.dump(result,open(out,'w'),indent=2)
print(json.dumps({k:v for k,v in result.items() if k!='local_axioms'},indent=2))
