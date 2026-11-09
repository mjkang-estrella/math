from pathlib import Path
import re,json
r=Path(__file__).resolve().parent.parent
sources={p.stem:p for p in (r/'src').glob('*.lean') if p.stem not in ['ClosureAudit','AuditR3']}
def closure(m):
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for i in re.findall(r'^import (\w+)',sources[n].read_text(),re.M):
   if i in sources:visit(i)
 visit(m);return sorted(seen)
cl=closure('BridgeTransport');(r/'outputs/endpoint-closure.json').write_text(json.dumps(cl,indent=2))
base=(r/'src/Audit.lean').read_text();code=base[base.index('import Lean.Util.CollectAxioms'):]
start=code.index('    if modName ==');end=code.index(' then\n',start)
for name,imports,mods in [('ClosureAudit',['BridgeTransport'],cl),('AuditR3',['Audit','BridgeTransport'],sorted(sources))]:
 replacement='    if '+ ' || '.join('modName == `'+m for m in mods)
 s=''.join('import '+m+'\n' for m in imports)+code[:start]+replacement+code[end:]
 verify='  let known : Array Name := #['+','.join('`'+m for m in sorted(sources))+']\n'
 verify+='  let expected : Array Name := #['+','.join('`'+m for m in mods)+']\n'
 verify+='  let actual := env.header.moduleNames.filter (known.contains ·)\n'
 verify+='  for m in known do\n    unless expected.contains m == actual.contains m do\n      throwError "Import closure mismatch: {m}"\n  for m in actual do\n    logInfo m!"AUDIT_MODULE {m}"\n'
 s=s.replace('  let mut count : Nat := 0\n',verify+'  let mut count : Nat := 0\n')
 s+=f'\n-- Expected audited local module set ({len(mods)} modules):\n'
 s+='-- '+','.join(mods)+'\n'
 s=s.replace('set_option pp.all false','set_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nset_option pp.all false')
 (r/'src'/f'{name}.lean').write_text(s)
