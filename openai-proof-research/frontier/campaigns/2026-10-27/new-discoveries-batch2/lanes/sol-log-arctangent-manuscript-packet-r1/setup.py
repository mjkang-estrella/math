from pathlib import Path
import json,hashlib,shutil
P=Path(__file__).resolve().parent; L=P.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x): (P/n).write_text(json.dumps(x,indent=2)+'\n')
F=L/'root-log-arctangent-formal-r1'; m=json.loads((F/'integrated-core-hashes.json').read_text())
assert all(h(F/n)==s for n,s in m['sha256'].items())
(P/'formal').mkdir(exist_ok=True); (P/'inputs').mkdir(exist_ok=True); (P/'supplement').mkdir(exist_ok=True)
inputs={}
for n,s in m['sha256'].items():
 inputs[str((F/n).relative_to(L))]=s
 shutil.copy2(F/n,P/('formal/'+Path(n).name if n.startswith('formal/') else 'inputs/'+Path(n).name))
shutil.copy2(F/'integrated-core-hashes.json',P/'inputs/integrated-core-hashes.json')
shutil.copy2(L/'root-gamma-level-complete-r3/pins.json',P/'pins.json')
for lane,names in {
'root-log-arctangent-formal-r1':['INTEGRATION.json','integrated-serial-replay.json'],
'root-log-arctangent-source-r3':['SOURCE-REVIEW.md','AUXILIARY.md','provenance.json','sources/publisher-canonical.pdf','sources/publisher-canonical.txt'],
'sol-log-arctangent-source-subsumption-r1':['review.md','stolarsky-2011.txt','refinements-2012.txt','new-means-2016.txt','chen-ratio.txt'],
'sol-log-arctangent-investment-review-r3':['review.md'],
'sol-log-arctangent-derivative-review-r2':['review.md','exact_review.py','exact-results.json'],
'root-log-arctangent-candidate-r1':['PROOF.md','exponential-terms.json'],
'root-log-arctangent-certificate-r2':['checks.json','verification.json','review-freeze.json'],
}.items():
 for n in names:
  src=L/lane/n; dst=P/'inputs'/lane/n; dst.parent.mkdir(parents=True,exist_ok=True)
  inputs[str(src.relative_to(L))]=h(src); shutil.copy2(src,dst)
dump('input-before.json',inputs)
# Adapt reviewed exact checker only for self-contained packet paths; mathematical operations unchanged.
s=(P/'inputs/sol-log-arctangent-derivative-review-r2/exact_review.py').read_text()
a=s.index('R=HERE.parent');b=s.index('# Q[d]')
s=s[:a]+"R=HERE.parent/'inputs/root-log-arctangent-certificate-r2'\nO=HERE.parent/'inputs/root-log-arctangent-candidate-r1'\n"+s[b:]
s=s.replace('\nintegrity()','')
(P/'supplement/exact_check.py').write_text(s)
# Exhaustive origin audit, not namespace filtering.
mods=m['mathematical_modules']
s='import SourceTheorem\nimport FiniteAbel\nimport Lean\nset_option autoImplicit false\nset_option warningAsError true\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.proofs false\nset_option pp.maxSteps 1000000\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  liftIO <| IO.FS.writeFile "dependencies.txt" (String.intercalate "\\n" (env.header.moduleNames.toList.map toString))\n  let mods := #['+','.join('`'+n for n in mods)+']\n  let allowed := #[`propext, `Classical.choice, `Quot.sound]\n  let mut count : Nat := 0\n  for i in [:env.header.moduleNames.size] do\n    let modName := env.header.moduleNames[i]!\n    if mods.contains modName then\n      for name in env.header.moduleData[i]!.constNames do\n        let ci := env.find? name |>.get!\n        let axs ← collectAxioms name\n        for ax in axs do\n          unless allowed.contains ax do\n            throwError "Forbidden dependency {name}: {ax}"\n        if ci.isUnsafe || ci.isAxiom then\n          throwError "Forbidden flag {name}"\n        logInfo m!"AUDIT {modName} {name}\\nTYPE {ci.type}\\nAXIOMS {axs}\\nFLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"\n        count := count + 1\n  logInfo m!"AUDIT_TOTAL {count}"\n'
(P/'formal/PacketAudit.lean').write_text(s)
print('Copied and verified',len(inputs),'inputs')
