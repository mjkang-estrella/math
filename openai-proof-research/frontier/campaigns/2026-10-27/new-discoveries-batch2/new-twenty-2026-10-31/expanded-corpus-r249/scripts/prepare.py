import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parents[1]; C=L.parent; B=C.parent
rs=json.loads((L/'reservation.json').read_text())['rows'];q=[]
for name,repo in [('openai','openai/math'),('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing')]:q.append((name+'-head','https://api.github.com/repos/'+repo+'/commits/HEAD'))
for r in rs:q.append((str(r['mathdb_id'])+'-abs',r['source_url']))
(L/'queue.json').write_text(json.dumps(q))
paths=[C/'ledger.json',B/'prior-campaign-context.json',B/'ledger.json']
o={}
for p in paths:
 if p.exists():
  v=json.loads(p.read_text());o[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':v.get('accepted'),'excluded':v.get('excluded',v.get('rejected'))}
(L/'inherited.json').write_text(json.dumps(o,indent=2))
pat='|'.join(str(r['mathdb_id']) for r in rs)
p=subprocess.run(['rg','-n','-m','3',pat,str(C),'--glob','*.md','--glob','results.json','--glob','!TASK.txt','--glob','!reservation.json'],capture_output=True,text=True)
(L/'historical-hits.txt').write_text(p.stdout)
