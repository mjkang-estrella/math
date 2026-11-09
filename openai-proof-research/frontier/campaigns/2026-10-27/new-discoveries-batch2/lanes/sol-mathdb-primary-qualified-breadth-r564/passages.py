import pathlib,json,re,hashlib
P=pathlib.Path(__file__).resolve().parent
for e in json.loads((P/'derivative-bindings.json').read_text()):
 b=pathlib.Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];t=b.decode();name=pathlib.Path(e['path']).stem
 print('\nSOURCE',name)
 if name=='korselt':print(t[:7000]);print(t[-3600:])
 if name=='recurrence':
  for term in ['(13)','(16)','Conjecture 2']:
   i=t.find(term);print(t[max(0,i-1800):i+1800])
 if name=='sandpile':
  a=t.find('Proposition 6.1');z=t.find('Conjecture 6.2');print(t[a:z]);print(t[z:z+2700])
# Required history: inspect all prior entries for matching IDs and summarize accepted families.
ids={r['mathdb_id'] for r in json.loads((P/'literal-records.json').read_text())}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 f=P.parent/'root-mathdb-accepted-exclusions-r304'/name;t=f.read_text();d=json.loads(t)
 print('PRIOR',name,'topkeys',list(d) if isinstance(d,dict) else len(d))
 for m in re.finditer('|'.join(map(str,ids)),t):print(t[max(0,m.start()-100):m.end()+250])
print('FULL344924',next(x['literal_statement'] for x in json.loads((P/'literal-records.json').read_text()) if x['mathdb_id']==344924))
