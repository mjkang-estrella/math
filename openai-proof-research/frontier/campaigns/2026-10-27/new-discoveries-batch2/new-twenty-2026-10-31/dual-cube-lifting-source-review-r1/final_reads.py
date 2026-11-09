import re,hashlib
print('ENTIRE CANDIDATE\n'+(a/'CANDIDATE.md').read_text())
s=(p/'qin2022.txt').read_text();i=s.index('Theorem 6.');j=s.find('4 ',i+1500);print('2022 THEOREM6 BODY',s[i:i+11000])
root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
for name in ['sources/upstream.json']:
 print(name,(root/name).read_text())
for parent in [p.parent.parent]:
 for name in ['ledger.json','prior-campaign-context.json']:
  q=parent/name
  if q.is_file():
   obj=json.loads(q.read_text());print(name,'keys',list(obj)[:30]);print('scalar metadata',{k:v for k,v in obj.items() if isinstance(v,(int,float,bool,str,type(None)))})
pin=root/'sources/CONTENTS.md';s=pin.read_text();print('PINNED catalog hash',hashlib.sha256(pin.read_bytes()).hexdigest(),'hits',{t:len(re.findall(t,s,re.I)) for t in ['dual.cube','independent spanning','CIST','376322']})
print('RAW PROVENANCE',json.dumps(json.loads((a/'provenance.json').read_text()).get('376322'),indent=2))
