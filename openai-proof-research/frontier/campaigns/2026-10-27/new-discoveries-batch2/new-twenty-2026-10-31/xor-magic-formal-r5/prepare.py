from pathlib import Path
import json,hashlib,re,shutil,zipfile
r=Path(__file__).resolve().parent
proof=sorted(p.stem for p in (r/'formal').glob('*.lean') if 'Audit' not in p.stem)
template=(r/'formal/AuditR4c.lean').read_text();body=template[template.index('import Lean'):]
for i in range(0,len(proof),15):
 group=proof[i:i+15];name=f'AuditAll{i//15}'
 s=''.join(f'import {m}\n' for m in group)+body
 s=s.replace('logs/audit-r4c-dag.jsonl',f'logs/audit-all-{i//15}-dag.jsonl')
 s=re.sub(r'\(\["ColourOrientation".*?\] : List String\)', '('+json.dumps(group)+' : List String)',s)
 (r/'formal'/f'{name}.lean').write_text(s)
# proof and audit modules, topologically sorted
sources={p.stem:p for p in (r/'formal').glob('*.lean')};order=[];done=set()
def visit(m):
 if m in done:return
 done.add(m)
 for line in sources[m].read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep in sources:visit(dep)
 order.append(m)
for m in sorted(sources):visit(m)
(r/'modules.json').write_text(json.dumps(order,indent=2)+'\n')
(r/'audit-groups.json').write_text(json.dumps([f'AuditAll{i//15}' for i in range(0,len(proof),15)]))
print(len(proof),len(order))
