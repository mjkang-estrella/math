from pathlib import Path
import runpy,json,time,random
R=Path(__file__).resolve().parents[1]
g=runpy.run_path(str(R/'work/flag-stable.py'),run_name='flaglib');stable=g['stable_ideals'];lex=g['lex'];direct=g['beta']
f=runpy.run_path(str(R/'packet/public/interval_betti.py'))['interval_betti']
start=time.monotonic();out=[]
for box in [(3,3,3),(2,2,2,3),(2,2,2,2,2),(2,2,2,2,2,2),(3,3,3,3)]:
 E,sets=stable(box);print('box',box,'sets',len(sets),flush=True)
 checked=0;found=None;limit=False
 for A in sets:
  for B in sets:
   if not B<=A:continue
   checked+=1;a=f(A,B,box);b=f(lex(A,E),lex(B,E),box)
   if any(v>b.get(k,0) for k,v in a.items()):
    found=dict(A=sorted(A),B=sorted(B),D=sorted(A-B),L=sorted(lex(A,E)-lex(B,E)),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
   if time.monotonic()-start>45:limit=True;break
  if found or limit:break
 o=dict(box=box,sets=len(sets),checked=checked,time_limit=limit,found=found);out.append(o);print(json.dumps(o),flush=True)
 if found or limit:break
(R/'packet/private/recursion-search.json').write_text(json.dumps(out,indent=2))
# Independently compare recurrence with direct modular Koszul for bounded stable pairs.
rng=random.Random(142);counts=0
for box in [(2,2,2),(2,2,3),(3,3,3),(2,2,2,2)]:
 E,sets=stable(box);pairs=[(A,B) for A in sets for B in sets if B<=A]
 for A,B in rng.sample(pairs,min(30,len(pairs))):
  assert f(A,B,box)==direct(A-B,box),(box,A,B);counts+=1
print('independent direct checks',counts,flush=True)
(R/'packet/private/recursion-direct-checks.json').write_text(json.dumps(dict(counts=counts,field=1000003,seed=142)))
