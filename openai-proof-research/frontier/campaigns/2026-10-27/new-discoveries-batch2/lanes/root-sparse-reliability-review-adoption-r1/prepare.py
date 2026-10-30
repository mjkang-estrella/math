from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='Sparse terminal-reliability independent ordinary MATH PASS and qualified SOURCE/SUBSTANTIVE PASS adopted for continued consideration. Printed Definition 9 discrepancy remains explicit. Novelty HOLD: actual 2025 predecessor DOI10.1016/j.procs.2025.10.297 and 2018 Networks bodies unread. Focused source-prior review assigned; no Lean/manuscript or credit. Root independent checker replay and freeze pass. See root-sparse-reliability-review-adoption-r1. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-sparse-reliability-preliminary-review-r1').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Adopt qualified sparse reliability review with prior-body holds')
(P/'integrate.py').write_text(t)
