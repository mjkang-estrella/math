from pathlib import Path
import ast
P=Path(__file__).resolve().parent
t=(P.parent/'root-r184-handback/integrate.py').read_text()
old=next(ast.literal_eval(n.value) for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='intro' for x in n.targets))
intro='Claude Opus5.5 high, standard speed is now the focused solver in claude-projection-packing-full-r1; r213/r214 remain broad scouts. r215 source inequality unresolved; symmetric cut cubes are excluded as counterexamples, arbitrary weighted-inverse shortcut fails, full column-packing lemma remains. Root scientific/reference/exact verification retained. See root-r215-handback. Breadth-plus-solving continues; counts 9 additional / 39 total, next 40.\n\n'
t=t.replace('sol-fresh-source-discovery-r184','sol-fresh-source-discovery-r215').replace(repr(old),repr(intro)).replace('Preserve uniform quadrature and rearrangement proof gaps','Hand projection constant full scope attack to Claude alongside scouts')
(P/'integrate.py').write_text(t)
