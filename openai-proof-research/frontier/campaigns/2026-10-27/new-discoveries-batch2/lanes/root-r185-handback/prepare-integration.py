from pathlib import Path
import ast
P=Path(__file__).resolve().parent
template=(P.parent/'root-r184-handback/integrate.py').read_text()
jobs={
185:('r185 full power-sum nonnormal-domain classification candidate retained; independent mathematical and classical-adaptation review assigned. Root exact replay and frozen originals pass; no Lean or acceptance. See root-r185-handback. Counts 9 additional / 39 total, next 40.','Retain power-sum domain candidate for independent review'),
186:('r186 uniform exact vertex-cover graph-counting question unresolved. Apex-family closed sum does not close global overlap compression or bit complexity. Root replay, 2527 originals/copies and manifest pass; fresh structural r188 assigned. See root-r186-handback. Counts 9 additional / 39 total, next 40.','Preserve exact graph-counting reductions and global gap'),
187:('r187 Brownian scalar crossing formula retained; proposed routine-adaptation exclusion sent for independent review. Full joint-process conjecture not proved; boundary-momentum question unresolved. Root replay and frozen originals pass. Active: power-sums review, Brownian review, fresh structural r188. See root-r187-handback. Counts 9 additional / 39 total, next 40.','Preserve Brownian scalar proof and independent eligibility review')}
old_intro=next(ast.literal_eval(n.value) for n in ast.parse(template).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='intro' for t in n.targets))
for number,(intro,message) in jobs.items():
 out=template.replace('sol-fresh-source-discovery-r184',f'sol-fresh-source-discovery-r{number}')
 out=out.replace(repr(old_intro),repr(intro+'\n\n'))
 out=out.replace('Preserve uniform quadrature and rearrangement proof gaps',message)
 assert intro in out
 (P.parent/f'root-r{number}-handback'/'integrate.py').write_text(out)
