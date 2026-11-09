import pathlib,re
P=pathlib.Path(__file__).parent
s=(P/'apn.txt').read_text()
for p in ['Conjecture','conjecture','Theorem 3','f_{b,c,r}','22']:
 for m in list(re.finditer(re.escape(p),s))[-2:]:print(p,s[max(0,m.start()-600):m.start()+2500])
s=(P/'billiards.txt').read_text();print('BILLIARDS BIB',s[s.find('References'):s.find('References')+11000])
