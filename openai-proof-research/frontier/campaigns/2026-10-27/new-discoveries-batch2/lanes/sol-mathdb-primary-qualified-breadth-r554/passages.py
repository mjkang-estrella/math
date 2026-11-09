import pathlib,json,hashlib,re
P=pathlib.Path(__file__).parent
for e in json.loads((P/'derivative-bindings.json').read_text()):
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=b.decode(); print('\nSOURCE',e['path'],s[:1000])
 patterns={'billiards.txt':['120','602','603','606','Proposition','References'], 'apn.txt':['Conjecture','Theorem 1','Theorem 2','8 ≤','22','References'],'postnikov.txt':['Theorem 3.3.','Theorem 3.4.','Theorem 4.1.','Theorem 6.3.']}[e['path']]
 for pattern in patterns:
  starts=[m.start() for m in re.finditer(re.escape(pattern),s)]
  for i in starts[:4]:print('\nMATCH',pattern,'OFFSET',i,'\n',s[max(0,i-500):i+2000])
