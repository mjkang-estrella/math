import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
# Independent coefficient extraction from path generating function, with e5=x,e6=y.
P={}
for t in range(125):
 for u in range(2):
  P[t,u]=4*P.get((t-1,u),0)+5*P.get((t,u-1),0)+int((t,u) in [(0,0),(1,0),(0,1)])
A=P[124,1];B=P[5,0];C=P[119,1];value=A-B*C
assert A==781*4**124 and B==5*4**4 and C==2999*4**118
assert value==-2499*4**122<0
out={'source_identity':'X_S(600,24,1)=X_P626+e1*X_P625-X_P25*X_P601','partition':{'6':1,'5':124},'N':626,'path626':A,'path25':B,'path601':C,'coefficient':value,'factored':'-2499*4^122','warning':'exact coefficient calculation, not a Lean proof of CSF semantics'}
(D/'outputs/spider-independent.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
