from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r205 Buczynski–Teitler–Woo Conjecture6.1 remains unresolved. Middle catalecticant injectivity in every dimension, degree and allowed characteristic is missing. Rational rank34/35 defeats the proposed moment-curve specialization, not the generic conjecture. Root private replay and original/copy/manifest verification pass. See root-r205-handback; fresh arithmetic r208 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r205').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve generic apolar Hilbert function gap and rank obstruction')
(P/'integrate.py').write_text(t)
