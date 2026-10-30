from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r207 Angelini lower intermediate-spectrum Question1 remains unresolved. Necessity and fixed-theta realizations are known; one prescribed-gap set realizing every theta still lacks simultaneous allocation and tail covers. Exact homogeneous-construction obstruction is not a source counterexample. Root replay and scientific/manifest/reference verification pass. See root-r207-handback; fresh analytic r209 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r207').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve lower intermediate spectrum realization gap')
(P/'integrate.py').write_text(t)
