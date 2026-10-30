from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r209-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r209','sol-fresh-source-discovery-r212')
v=v.replace("['diversity','bcc','bcc-stability']","['karam','lim']").replace("name+'-extraction.stderr'","name+'.extract.stderr'")
v=v.replace('Pointwise-tail route falsifier and finite rational controls only; no full lattice moment or integrated-tail theorem.','Finite metric-graph controls and all-vertices route obstruction only; no uniform common-center theorem.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r212 Karam common-center ConjectureD remains unresolved. Exact cubic averaging gives a root at each radius; the finite-intersection property needed for one root at every radius is unproved. Entropy supplies eventual growth only; dumbbell refutes all-root strengthening, not source. Root exact/extraction/scientific/reference checks pass. See root-r212-handback; fresh analytic r215 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r212').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve common center graph growth quantifier gap')
(P/'integrate.py').write_text(t)
