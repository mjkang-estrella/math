from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r188 Bonnet triangle-partition sidestep Question 5 remains unresolved. Wedge-factor and matching-blocker reductions do not supply uniform polynomial search; exact method counterexamples retained. Root 32768-graph replay and frozen evidence pass. See root-r188-handback. Fresh structural r191 assigned; arithmetic r189 and analytic r190 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r188').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve triangle-partition sidestep reductions and algorithmic gap')
(P/'integrate.py').write_text(t)
