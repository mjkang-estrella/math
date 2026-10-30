from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='r196 full sparse three-constrained terminal-reliability ordinary proof candidate retained for independent adversarial review. Conditional TP2 association and edge-budget replacement bridge supplied; printed graph-indexing qualification and unread 2025 proceedings remain HOLD. Root exact replays and scientific/manifest integrity pass. See root-r196-handback; sparse-reliability preliminary review assigned. No Lean, paper or credit; counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r196').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Preserve sparse terminal-reliability candidate for independent review')
(P/'integrate.py').write_text(t)
