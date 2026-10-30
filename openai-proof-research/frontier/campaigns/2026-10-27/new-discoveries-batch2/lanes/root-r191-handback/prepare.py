from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r188-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r188','sol-fresh-source-discovery-r191').replace("j['exclusions']","j['excludes']").replace('history-receipt.json','raw-history-inventory.json').replace('Finite exact reductions and method obstructions; no polynomial-time algorithm or source refutation.','Finite coset and double-cover controls; full automorphism construction remains missing.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r191 semisymmetric graph semiregular-automorphism question remains unresolved. Two-coset route lacks full automorphism control; double cover/subdivision/product transfers fail. Root exact replay and freezes pass; overinclusive retained history is not qualified unique coverage. See root-r191-handback. Fresh structural r193 assigned; Guo review and analytic r192 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r191').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve semisymmetric graph route and full-automorphism gap')
(P/'integrate.py').write_text(t)
