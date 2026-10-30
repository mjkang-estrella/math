from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-power-sums-domain-review-adoption-r1/verify.py').read_text()
v=v.replace('sol-power-sums-domain-preliminary-review-r1','sol-brownian-affine-scalar-preliminary-review-r1').replace('final-manifest.json','finalmanifest.json').replace("m['excluded']","m['explicit_exclusions']").replace("['scientific']","['inputs']").replace("r['bytes']","r.get('bytes',r.get('size'))").replace('independent_check.py','checker.py').replace('independent-evidence.json','checker-evidence.json')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='Brownian affine scalar formula: root adopts ordinary SOURCE/MATH PASS and routine classical-adaptation exclusion after independent compensation/martingale bridge. Full joint-process Conjecture 1.4 remains outside proof; Grandits priority body unread/HOLD. Root exact replay and 60 original/copy pairs pass. See root-brownian-affine-review-adoption-r1. Fresh analytic r190 assigned; structural r188 and arithmetic r189 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-brownian-affine-scalar-preliminary-review-r1').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Adopt Brownian scalar proof and classical-adaptation exclusion')
(P/'integrate.py').write_text(t)
