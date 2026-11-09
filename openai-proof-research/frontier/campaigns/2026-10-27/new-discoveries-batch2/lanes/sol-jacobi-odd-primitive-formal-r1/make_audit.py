#!/usr/bin/env python3
"""Generate a literal all-declaration audit from the actual imported environment."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
s=(ROOT/'verification/inventory-development-runner.log').read_text()
mods=dict(re.findall(r'^ODD_PRIMITIVE_MODULE (\S+) (\S+)$',s,re.M))
names=set(re.findall(r'^ODD_PRIMITIVE_DECL (\S+)$',s,re.M))
safety=dict(re.findall(r'^ODD_PRIMITIVE_SAFETY (\S+) (true|false)$',s,re.M))
assert set(mods)==names==set(safety) and all(v=='false' for v in safety.values())
explicit={}
for mod in set(mods.values()):
 for n in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:def|abbrev|theorem)\s+(\w+)',(ROOT/'formal'/f'{mod}.lean').read_text(),re.M):
  explicit['JacobiShifted.MidpointRational.'+n]=mod
assert set(explicit)<=names,set(explicit)-names
rows=[dict(name=n,source_module=mods[n],kind='explicit' if n in explicit else 'generated auxiliary') for n in sorted(names)]
(ROOT/'declarations.json').write_text(json.dumps(rows,indent=2)+'\n')
out='import OddPrimitiveSequence\n\nset_option autoImplicit false\nset_option warningAsError true\n-- Compiler auxiliaries are intentionally included in this exhaustive audit.\nset_option linter.auxLemma false\n\n'
for row in rows:
 n=row['name'];out+=f'#check {n}\n#print axioms {n}\n\n'
(ROOT/'formal/OddPrimitiveAudit.lean').write_text(out)
print(json.dumps({'all_declarations':len(rows),'explicit':len(explicit),'generated':len(rows)-len(explicit),'all_safe':True},indent=2))
