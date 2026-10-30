from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r206 Easlick minimal-winning dice maximum-cycle conjecture remains unresolved. Common padding fails beyond even-to-odd single-face embedding; unrestricted probability realization does not preserve face and label budgets. Root graph replay and scientific/manifest/reference verification pass. See root-r206-handback; fresh structural r210 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r206').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve minimal winning dice cycle gap and padding obstruction')
(P/'integrate.py').write_text(t)
