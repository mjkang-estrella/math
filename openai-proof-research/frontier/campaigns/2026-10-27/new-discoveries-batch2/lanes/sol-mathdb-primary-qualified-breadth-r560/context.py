import pathlib,json,hashlib
D=pathlib.Path(__file__).parent; L=D.parent;A=json.loads((D/'assigned-records.json').read_text());ids={x['record']['mathdb_id'] for x in A}
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 t=(L/'root-mathdb-accepted-exclusions-r304'/n).read_text();j=json.loads(t)
 print(n,'keys',list(j));print('assigned exact IDs mentioned',[i for i in sorted(ids) if str(i) in t])
 if 'families' in j:
  for x in j['families']:print(x.get('number'),x.get('title'),x.get('scope',x.get('source_target')))
for fn,pat,count in [('irregular.txt','Conjecture 1.1',1700),('irregular.txt','Theorem 2.1 .',2400),('plactic.txt','Theorem 2.8 .',3500),('idp.txt','positive integers',1000),('idp-successor.txt','2.2',800)]:
 t=(D/fn).read_text();p=t.find(pat);print('\n',fn,pat,p,t[max(0,p-150):p+count])
