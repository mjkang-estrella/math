from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r203-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r203','sol-fresh-source-discovery-r202').replace("m['excludes']","m['excluded_explicitly']")
v=v.replace("aliases=json.loads((S/'legacy-alias-refresh.json').read_text())['records']", "aliases=json.loads((S/'index-bindings.json').read_text())+json.loads((S/'context-bindings.json').read_text())")
v=v.replace('Exact radix and support controls only; no universal additive-complement gap theorem.','Exact local excess and progression-sum arithmetic controls only; no universal regular-sequence boundary theorem.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r202 regular-sequence additive-bases boundary conjecture remains unresolved. Known upper bounds do not attain the target; the p=3 defect argument does not extend uniformly. Root exact replay and primary/manifest integrity pass; local nonprogression witness is not a source refutation. See root-r202-handback; fresh structural r206 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r202').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve regular sequence boundary gap and exact obstruction')
(P/'integrate.py').write_text(t)
