import pathlib,json
L=pathlib.Path(__file__).resolve().parent
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text()); print(n,'keys',list(d))
 if n=='ledger.json':print('counts',{k:d[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
 for k,v in d.items():
  if isinstance(v,list):
   print(k,'records',len(v))
   for x in v:
    if any(w in json.dumps(x).lower() for w in ['floor','jacobsthal']):print(json.dumps(x)[:3000])
rows=[]
for p in sorted(L.glob('th_lemma_*.guard.json')):
 r=json.loads(p.read_text()); rows.append({'module':p.name.split('.')[0],**r})
print('arithmetic modules',len(rows),'PASS',sum(r['exit_code']==0 for r in rows))
print('failures',[(r['module'],r['reason']) for r in rows if r['exit_code']])
