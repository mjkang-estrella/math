from run import *
out=[run('build-V3Config355701-AS64',[str(B/'lean'),'-j1','-DwarningAsError=true','-o','V3Config355701.olean','V3Config355701.lean'])]
for m in ['Yip355956','V3Config355701']:
 s=f'''import {m}
set_option pp.all true
set_option pp.proofs true
open Lean in
elab "#origin_audit" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{m} | throwError "module absent"
  let mut names := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    logInfo m!"ORIGIN {{n}}"
    Elab.Command.elabCommand (← `(#print $(mkIdent n)))
    Elab.Command.elabCommand (← `(#print axioms $(mkIdent n)))
  logInfo m!"ORIGIN_COUNT {{names.size}}"
#origin_audit
'''
 (L/f'Origin{m}.lean').write_text(s)
 out.append(run('origin-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true',f'Origin{m}.lean']))
 out.append(run('checker-'+m,[str(B/'leanchecker'),m]))
(D/'audits.json').write_text(json.dumps(out,indent=2))
