from run import *
out=[]
for m in ['Yip355956','V3Config355701']:
 s=f'''import {m}
open Lean in
elab "#flags" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{m} | throwError "missing module"
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      logInfo m!"FLAG {{n}} unsafe={{ci.isUnsafe}} partial={{ci.isPartial}} axiom={{ci.isAxiom}}"
      count := count + 1
  logInfo m!"FLAG_COUNT {{count}}"
#flags
'''
 (L/f'Flags{m}.lean').write_text(s);out.append(run('flags-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true',f'Flags{m}.lean']))
(D/'flags.json').write_text(json.dumps(out,indent=2))
