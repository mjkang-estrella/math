from pathlib import Path
import runpy,json
R=Path(__file__).resolve().parents[1];g=runpy.run_path(str(R/'work/flag-stable.py'),run_name='flaglib');stable=g['stable_ideals'];lex=g['lex']
f=runpy.run_path(str(R/'packet/public/interval_betti.py'))['interval_betti']
# Look for a concrete failure of *termwise* endpoint comparison only.
for box in [(2,2,2,2),(3,3,3),(2,2,2,2,2)]:
 E,sets=stable(box);found=None
 for A in sets:
  for B in sets:
   if not B<=A:continue
   LA,LB=lex(A,E),lex(B,E)
   for end in [0,box[-1]-1]:
    sl=lambda X:frozenset(u[:-1] for u in X if u[-1]==end)
    a=f(sl(A),sl(B),box[:-1]);b=f(sl(LA),sl(LB),box[:-1])
    if any(v>b.get(k,0) for k,v in a.items()):
     found=dict(box=box,A=sorted(A),B=sorted(B),LA=sorted(LA),LB=sorted(LB),end=end,endpoint_actual={str(k):v for k,v in a.items()},endpoint_lex={str(k):v for k,v in b.items()},whole_actual={str(k):v for k,v in f(A,B,box).items()},whole_lex={str(k):v for k,v in f(LA,LB,box).items()});break
   if found:break
  if found:break
 if found:
  print(json.dumps(found,indent=2));(R/'packet/private/endpoint-check.json').write_text(json.dumps(found,indent=2));break
