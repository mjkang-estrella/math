from pathlib import Path
import importlib.util,os,json
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('v',P/'extracted/verify.py');v=importlib.util.module_from_spec(spec)
import sys
sys.path.insert(0,str(P/'extracted'));spec.loader.exec_module(v)
pins=v.assert_pins();out=P/'extracted/own-replay';env=dict(os.environ,LEAN_PATH=str(out)+':'+':'.join(d['path']+'/.lake/build/lib/lean' for d in pins['packages'].values()))
mods=json.loads((P/'extracted/inputs/integrated-core-hashes.json').read_text())['mathematical_modules']
# All modules available now; no broad import Lean. Independently compare the entire kernel map
# by actual module origin, and separately inventory codegen extra names without inventing types.
s='import SourceTheorem\nimport FiniteAbel\nset_option autoImplicit false\nset_option warningAsError true\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let mods := #['+', '.join('`'+m for m in mods)+']\n  let mut total := 0\n  for i in [:env.header.moduleNames.size] do\n    let modName := env.header.moduleNames[i]!\n    if mods.contains modName then\n      let data := env.header.moduleData[i]!\n      let mut actual : Array Name := #[]\n      for (n, _) in env.constants.toList do\n        if env.getModuleIdxFor? n == some i then\n          actual := actual.push n\n      unless actual.size == data.constNames.size && actual.all data.constNames.contains do\n        throwError "Origin mismatch {modName}"\n      total := total + actual.size\n      logInfo m!"ORIGIN {modName} {actual.size}"\n      for n in data.extraConstNames do\n        match env.find? n with\n        | none => logInfo m!"IR_ONLY {modName} {n}: no kernel declaration/type"\n        | some ci => logInfo m!"EXTRA_KERNEL {modName} {n}: {ci.type}; unsafe={ci.isUnsafe}"\n  logInfo m!"ORIGIN_TOTAL {total}"\n#print LogArctangentSource.SourceClaim\n#print LogArctangentSource.source_conjecture37\n#print axioms LogArctangentSource.source_conjecture37\n'
(out/'OwnOrigin.lean').write_text(s)
r=v.run([pins['lean_binary'],'-j1','-DwarningAsError=true','-DautoImplicit=false','OwnOrigin.lean'],out,P/'own-origin.log',env)
(P/'own-origin-receipt.json').write_text(json.dumps(r,indent=2))
