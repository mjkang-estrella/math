from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r198-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r198','sol-fresh-source-discovery-r200').replace("(S/'checks-final.json')","(S/'checks.json')")
v=v.replace("for r in json.loads((S/'scientific-freeze.json').read_text())]","for r in json.loads((S/'scientific-freeze.json').read_text())+json.loads((S/'primary-freeze.json').read_text())]")
v=v.replace('Inherited failures preserved.','First-read freezing deviation preserved; final-freeze integrity only.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r200 radial convexity / fixed-degree matrix monotonicity Conjecture 4.10 remains unresolved. Global derivative positivity recovery for all n>=3 and arbitrary-function regularity remain unproved; positive Hadamard-square rational witness is only a pointwise method obstruction. Root replay and actual final-freeze verification pass; first-read freezing deviation retained. See root-r200-handback. Fresh analytic r201 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r200').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve radial convexity positivity gap and exact obstruction')
(P/'integrate.py').write_text(t)
