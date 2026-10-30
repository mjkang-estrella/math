from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r192 Kovalev linear Lipschitz clustering Question 6.5 remains unresolved. Per-space/uniform reduction and collision criterion retained; all-space linear stability missing. Method obstructions are not source refutations. Root exact replay and scientific/manifest verification pass. See root-r192-handback. Fresh analytic r195 assigned; structural r193 and arithmetic r194 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r192').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve Lipschitz clustering reductions and uniform stability gap')
(P/'integrate.py').write_text(t)
