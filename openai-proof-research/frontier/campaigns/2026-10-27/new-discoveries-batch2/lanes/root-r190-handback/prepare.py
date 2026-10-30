from pathlib import Path
import ast
P=Path(__file__).resolve().parent;t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r190 five-frequency cosine sign-agreement optimum remains unresolved; published possible-candidate attribution is not a numbered conjecture. Joint correlation/classification gap remains despite parity/scale reductions. Root exact replay and 5119 original/copy pairs pass. See root-r190-handback. Fresh analytic r192 assigned; Guo review and structural r191 continue. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r190').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve five-frequency cosine reductions and universal gap')
(P/'integrate.py').write_text(t)
