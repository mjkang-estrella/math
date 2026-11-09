from pathlib import Path
import json,re
r=Path(__file__).resolve().parent
p=r/'formal/Probe.lean'
if p.exists():p.rename(r/'logs/Probe.lean')
p=r/'formal/Probe.olean'
if p.exists():p.unlink()
mods={p.stem:p for p in (r/'formal').glob('*.lean') if p.stem!='AuditR6'}
order=[];seen=set()
def visit(m):
 if m in seen or m not in mods:return
 seen.add(m)
 for ln in mods[m].read_text().splitlines():
  if ln.startswith('import '):
   for dep in ln.split()[1:]:visit(dep)
 order.append(m)
for m in sorted(mods):visit(m)
base=(r/'formal/AuditR4.lean').read_text();body=base[base.index('set_option pp.all true'):]
start=body.index('#[`Audit,');end=body.index('].contains m',start)+1
body=body[:start]+'#['+', '.join('`'+m for m in order)+']'+body[end:]
(r/'formal/AuditR6.lean').write_text(''.join('import '+m+'\n' for m in order)+body)
(r/'modules.json').write_text(json.dumps(order+['AuditR6'],indent=2)+'\n')
s=(r/'inherited/replay.py').read_text()
a=s.index("if (root/'formal/Coverage8.lean').exists():");b=s.index("(root/'logs/replay.json').write_text",a)
s=s[:a]+s[b:]
s=s.replace('PASS PARTIAL r5p PACKET ONLY','PASS Coverage8 AND CONDITIONAL ENDPOINT r6p').replace('INCOMPLETE r5p packet','r6p Coverage8 and conditional endpoint packet')
s=s.replace('for name,source in controls.items():', '''controls['FourNeighbors'] = 'import Coverage8\\nexample : Nut8.eligibleNeighbors 4 0 15 = true := by\\n  decide +kernel\\n'
controls['FullOldDegree'] = 'import Coverage8\\nexample : Nut8.eligibleNeighbors 4 31710 1 = true := by\\n  decide +kernel\\n'
controls['MissingPerSupport'] = 'import FinalEndpoint\\nexample : Nut8.Target := by\\n  exact Nut8.nut8_target\\n'
for name,source in controls.items():''')
(r/'replay.py').write_text(s)
print(len(order)+1,'modules')
