from pathlib import Path
import json,itertools
D=Path(__file__).parent
C=[]
for n in range(1,9):
 for a in itertools.product('147',repeat=n):
  c4=a.count('4');c7=a.count('7')
  if (n==8 and c4<=2 and c7<=1) or (n<8 and c4==2 and c7==1):C.append(int(''.join(a)))
assert not any(x%256==0 for x in C)
assert 111744%128==0 and 111744%256!=0
r={'status':'PASS','target':352158,'known_source_instance_only':True,'Ce_size':len(C),'e':8,'divisible_by_256':0,'witness':111744,'valuation_2':7,'universal_conjecture_proved':False,'accepted_credit':0,'scope':'Lemma 1 finite suffix test for exactly two 4 digits, one 7, arbitrary 1 digits. Published example, no new result.'}
(D/'cheap-check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
