from pathlib import Path
import json
r=Path(__file__).resolve().parent
mods={p.stem:p for p in (r/'formal').glob('*.lean') if p.stem not in ['FinalEndpoint','AuditAll']}
order=[];seen=set()
def visit(m):
 if m in seen or m not in mods:return
 seen.add(m)
 for ln in mods[m].read_text().splitlines():
  if ln.startswith('import '):
   for dep in ln.split()[1:]:visit(dep)
 order.append(m)
for m in sorted(mods):visit(m)
base=(r/'formal/AuditR4.lean').read_text()
body=base[base.index('set_option pp.all true'):]
start=body.index('#[`Audit,');end=body.index('].contains m',start)+1
body=body[:start]+'#['+', '.join('`'+m for m in order)+']'+body[end:]
(r/'formal/AuditAll.lean').write_text(''.join('import '+m+'\n' for m in order)+body)
order+=['AuditAll']
(r/'modules.json').write_text(json.dumps(order,indent=2)+'\n')
s=(r/'replay_r4.py').read_text().replace('PASS PARTIAL r4b PACKET ONLY','PASS PARTIAL r5p PACKET ONLY').replace('INCOMPLETE r4b packet','INCOMPLETE r5p packet')
s=s.replace("for name,source in controls.items():",'''controls['WrongMask'] = 'import TransportedNeighbors\\nexample : (Nut8.transportedMask (⊥ : SimpleGraph (Fin 2)) 0 (Equiv.refl _)).testBit 0 = true := by\\n  rw [Nut8.transportedMask_bit]\\n  simp\\n'
controls['WrongEncoding'] = 'import ExtensionEncoding\\nexample : Nut8.graphBit 2 (Nut8.extendGraph 1 0 1) 0 0 = true := by\\n  decide +kernel\\n'
controls['MissingCoverage'] = 'import FiniteOfParts\\nexample : Nut8.Coverage8 := by\\n  exact Nut8.coverage8\\n'
controls['MissingFiniteObstruction'] = 'import EndpointOfParts\\nexample : Nut8.FiniteObstruction := by\\n  exact Nut8.finite_obstruction\\n'
for name,source in controls.items():''')
s=s.replace("(root/'logs/replay.json').write_text",'''if (root/'formal/Coverage8.lean').exists():
 run('strict-FinalEndpoint.log',[lean,'-j1','-DwarningAsError=true','-o',root/'formal/FinalEndpoint.olean',root/'formal/FinalEndpoint.lean'])
 run('leanchecker-FinalEndpoint.log',[lean.parent/'leanchecker','FinalEndpoint'])
else:
 (root/'logs/conditional-assembly.json').write_text(json.dumps({'status':'SKIPPED','reason':'Coverage8.lean is absent; nut8_target has not been checked.'},indent=2)+'\\n')
(root/'logs/replay.json').write_text''')
(r/'replay.py').write_text(s)
print(len(order),'modules')
