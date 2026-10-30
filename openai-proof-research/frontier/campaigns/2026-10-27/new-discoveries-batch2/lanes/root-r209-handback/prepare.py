from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r209 BCC global lattice moment optimality for every real p>=1 remains unresolved. Pointwise radial-tail domination is false against FCC; the sufficient integrated-tail comparison is unproved. Dajani collar separation is routine under its literal interpretation and does not settle stronger free-boundary structure. Root source/extraction/exact replay and references pass. See root-r209-handback; fresh analytic r212 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r209').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve all parameter BCC moment gap and radial tail obstruction')
(P/'integrate.py').write_text(t)
