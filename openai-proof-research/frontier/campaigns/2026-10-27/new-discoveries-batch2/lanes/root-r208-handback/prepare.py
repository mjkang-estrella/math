from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r208 Casas–Madrid–Rosales Conjecture41 remains unresolved. Ratio deletion enumerates the fixed-invariant family but the first-internal-ancestor map is not injective; uniform inclusion-neighborhood Hall inequality is missing. Root exact replay and scientific/manifest/reference verification pass. See root-r208-handback; fresh arithmetic r211 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r208').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve numerical semigroup leaf count gap and Hall obstruction')
(P/'integrate.py').write_text(t)
