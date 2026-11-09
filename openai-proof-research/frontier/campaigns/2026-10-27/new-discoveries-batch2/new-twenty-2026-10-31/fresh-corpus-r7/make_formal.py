from pathlib import Path
from itertools import permutations
w=Path(__file__).parent
adj=lambda u,v:u!=v and ((u<4 and v<4) or (u<4 and v>=4 and u//2==(v-4)//2) or (v<4 and u>=4 and v//2==(u-4)//2))
rows=[]
for s in range(4):
 rr=[]
 for u in range(8):
  r=[]
  for v in range(8):
   C=list(range(4))+[s+4]; found=None
   if adj(u,v):
    for t in range(4):
     D=list(range(4))+[t+4]
     for dest in permutations(D):
      if all(x==y or adj(x,y) for x,y in zip(C,dest)) and any((x==u and y==v) or (x==v and y==u) for x,y in zip(C,dest)):
       f=list(range(8))
       for x,y in zip(C,dest):f[x]=y
       found=(t,f);break
     if found:break
    assert found,(s,u,v)
   else:found=(s,list(range(8)))
   r.append(found)
  rr.append(r)
 rows.append(rr)
def vec(l):return '!['+', '.join(map(str,l))+']'
(w/'packet/Response.leanfrag').write_text('def nextState : Fin 4 → Fin 8 → Fin 8 → Fin 4 :=\n'+vec([vec([vec([rows[s][u][v][0] for v in range(8)]) for u in range(8)]) for s in range(4)])+'\n\ndef response : Fin 4 → Fin 8 → Fin 8 → Fin 8 → Fin 8 :=\n'+vec([vec([vec([vec(rows[s][u][v][1]) for v in range(8)]) for u in range(8)]) for s in range(4)])+'\n')
