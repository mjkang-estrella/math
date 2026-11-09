import pathlib,json,hashlib,re
P=pathlib.Path(__file__).parent;out=[]
for e in json.loads((P/'derivative-bindings.json').read_text()):
 b=(P/e['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size'];s=b.decode()
 patterns={'billiards.txt':['3.7.','[9]','[6]'],'apn.txt':['Theorem 1.1 .','Theorem 4.5 .','Conjecture 4.7 .'],'postnikov.txt':[],'billiard-companion.txt':['Theorem','Proposition','foci','pedal']}[e['path']]
 for pattern in patterns:
  matches=list(re.finditer(re.escape(pattern),s)); matches=matches[-1:] if pattern.startswith('[') else matches[:3]
  for m in matches:
   passage=s[max(0,m.start()-200):m.start()+2300];out.append({'file':e['path'],'start':max(0,m.start()-200),'passage':passage});print(e['path'],pattern,re.sub(r'\s+',' ',passage))
(P/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
