d=json.loads(read(L/'provenance.json'))
for i in ['372614','372494']: print(i,d[i]['record']['statement'])
h=json.loads(read(L/'history-matches.json'))
for x in h:
 print('HISTORY',x['path'])
 c=x['content']; rows=c.items() if isinstance(c,dict) else enumerate(c)
 for k,v in rows:
  t=json.dumps(v,ensure_ascii=False)
  if any(s in t for s in x['source_families']+['372614']): print(k,t[:6000])
for p in sorted((L/'sources').glob('*html.txt')):
 s=read(p).decode(); terms=['conjecture','conjectured','question','counterexample','definition']
 print('BODY',p.name,len(s))
 for m in list(re.finditer('|'.join(terms),s,re.I))[-12:]: print(s[max(0,m.start()-160):m.start()+850].replace('\n',' ')[:1010])
