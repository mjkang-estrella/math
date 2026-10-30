from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r188-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r188','sol-fresh-source-discovery-r193').replace("j['exclusions']","j['excluded']").replace("['scientific-freeze.json','finalmanifest.json']","['scientific-input-freeze.json','scientific-freeze.json','finalmanifest.json']").replace('Finite exact reductions and method obstructions; no polynomial-time algorithm or source refutation.','Finite regular-graph controls and local-method obstruction; universal extremal clique-forcing remains missing.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r193 Romero–Petingi Conjecture 10 remains unresolved in full scope. Exact equivalence requires a clique component in every regular triangle maximizer at all feasible N>=2(d+1); large-order comparison does not close it. Corrected checker and root freeze verification pass; initial faulty pruning preserved. See root-r193-handback. Fresh structural r196 assigned; arithmetic r194 and analytic r195 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r193').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve regular triangle-maximizer reduction and universal gap')
(P/'integrate.py').write_text(t)
