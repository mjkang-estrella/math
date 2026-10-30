from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='Guo divisibility review: root adopts SOURCE/ordinary MATH PASS and routine complete-adaptation exclusion. Published stronger endpoint preserved, historical novelty HOLD separate. Root independent-checker replay, 75 original/copy pairs and 109-entry manifest pass. See root-guo-divisibility-review-adoption-r1. Fresh arithmetic r194 assigned; analytic r192 and structural r193 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-guo-divisibility-preliminary-review-r1').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Adopt Guo divisibility proof and routine-adaptation exclusion')
(P/'integrate.py').write_text(t)
