from pathlib import Path
import ast
P=Path(__file__).resolve().parent
v=(P.parent/'root-r203-handback/verify.py').read_text().replace('sol-fresh-source-discovery-r203','sol-fresh-source-discovery-r204').replace("m['excludes']","m['exclusions']").replace('legacy-alias-refresh.json','alias-refresh.json')
v=v.replace('Exact radix and support controls only; no universal additive-complement gap theorem.','Exact source rank and isolated-fiber controls only; no universal medial-axis necessity theorem.')
(P/'verify.py').write_text(v)
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r204 medial-axis rectifiability Question2 remains unresolved. Rank preservation is publicly sufficient; derivative rank loss alone does not realize an exact higher-dimensional equidistance fiber. Root replay and frozen primary/manifest integrity pass. See root-r204-handback; fresh analytic r207 assigned. Counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r204').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve medial axis necessity gap and isolated fiber obstruction')
(P/'integrate.py').write_text(t)
