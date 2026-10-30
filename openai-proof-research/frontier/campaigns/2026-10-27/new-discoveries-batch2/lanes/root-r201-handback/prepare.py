from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r201 Nielsen–Okamura smooth dual-midpoint rigidity remains unresolved; rank-one cubic has nontrivial pointwise derivative kernel, not an exact midpoint counterexample. Degenerate strata and smooth higher-order control remain open. Fractional Korn extension excluded by actual public full bridge. Root symbolic replay and primary/manifest/snapshot integrity pass. See root-r201-handback; fresh analytic r204 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r201').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve dual midpoint rigidity gap and exact tensor kernel')
(P/'integrate.py').write_text(t)
