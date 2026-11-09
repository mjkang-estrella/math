# cross-check lemma formulas with the independent memoised Python implementation gam.py
from gam import G,IN as gIN,OUT as gOUT,F as gF
import lemmas as Lm
mp={Lm.IN:gIN,Lm.OUT:gOUT,Lm.F:gF}
bad=0;n=0
for k in range(1,41):
    for i in range(1,41):
        for a in (Lm.IN,Lm.OUT):
            for b in (Lm.IN,Lm.OUT):
                n+=2
                bad+= G('I',(k,mp[a]),(i,mp[b]))!=Lm.L1(k,a,i,b)
                bad+= G('N',(1,gF),(k,mp[a]),(i,mp[b]))!=Lm.L4(k,a,i,b)
                # O-centre = reversal
                n+=1; bad+= G('O',(k,mp[a]),(i,mp[b]))!=Lm.L1(k,Lm.flip(a),i,Lm.flip(b))
for i in range(1,201):
    for b in (Lm.IN,Lm.OUT,Lm.F):
        n+=1; bad+= G('I',(1,gF),(i,mp[b]))!=Lm.L2(i,b)
for y in range(2,25,2):
    for i in range(1,61):
        for b in (Lm.IN,Lm.OUT):
            n+=2
            bad+= G('I',(y,gF),(i,mp[b]))!=Lm.L3(y,i,b)
            bad+= G('N',(1,gF),(y,gF),(i,mp[b]))!=Lm.L5(y,i)
for y in range(4,17,2):
    for z in range(y+2,y+40):
        n+=1; bad+= G('N',(1,gF),(y,gF),(z,gF))!=Lm.gform(y,z)
print('checks',n,'bad',bad)
