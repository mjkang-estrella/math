from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r189 full Guo divisibility Conjecture 2 ordinary candidate retained; factorial-basis and valuation bridge needs independent math/substantive adjudication. Root exact replay and 2577 original/copy pairs pass. Independent Guo review assigned; analytic r190 and structural r191 continue. See root-r189-handback. No Lean or manuscript; counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r189').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Retain Guo divisibility proof for independent review')
(P/'integrate.py').write_text(t)
