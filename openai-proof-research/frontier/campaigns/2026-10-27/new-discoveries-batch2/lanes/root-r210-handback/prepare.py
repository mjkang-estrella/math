from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r210 four-color t-chromatic caterpillar reconstruction remains unresolved. Exact transfer and color-subset inversion give four scalar polynomials, but rigidity up to spine reversal is unproved; full U-polynomial reconstruction does not decode this specialization. Root checks and scientific/manifest/reference verification pass. See root-r210-handback; fresh structural r213 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r210').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve four color caterpillar reconstruction gap')
(P/'integrate.py').write_text(t)
