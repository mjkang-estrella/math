from run import *
out=[]
for m in ['Yip355956','V3Config355701']:
 p=L/f'Origin{m}.lean';s=p.read_text().replace('set_option pp.proofs true','set_option pp.proofs true\nset_option pp.deepTerms true\nset_option pp.maxSteps 100000000\nset_option maxRecDepth 1000000')
 s=s.replace('logInfo m!"ORIGIN {n}"','let some ci := env.find? n | throwError "missing declaration"\n    logInfo m!"ORIGIN {n} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"')
 p.write_text(s);out.append(run('full-origin-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true',p.name]))
(L/'FalseYipFinite.lean').write_text('import Yip355956\nexample : 3 ∣ (5^8-1) / (5^2-1) := by decide +kernel\n')
out.append(run('negative-FalseYipFinite',[str(B/'lean'),'-j1','-DwarningAsError=true','FalseYipFinite.lean']))
(D/'full-audits.json').write_text(json.dumps(out,indent=2))
