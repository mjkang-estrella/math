from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='Power-sum Remark 3.3(4): root adopts full ordinary proof/source PASS and routine source/classical-adaptation exclusion after independent complete bridge. Novelty remains bounded/HOLD; no Lean or manuscript. Root exact replay, 81 original/copy pairs and 102-entry review manifest pass. See root-power-sums-domain-review-adoption-r1. Fresh arithmetic r189 assigned; Brownian review and structural r188 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-power-sums-domain-preliminary-review-r1').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Adopt power-sum ordinary proof and routine-exclusion review')
(P/'integrate.py').write_text(t)
