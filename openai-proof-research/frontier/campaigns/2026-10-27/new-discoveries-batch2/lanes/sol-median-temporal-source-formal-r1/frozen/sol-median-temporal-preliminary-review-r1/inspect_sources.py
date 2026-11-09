from pathlib import Path
import json,subprocess,hashlib,urllib.request,urllib.error,datetime
L=Path(__file__).resolve().parent
for name in ['1911.08613v2','1207.0893v1','1902.03349v2','1912.06524v2']:
 p=L/'frozen/frozen'/f'{name}.pdf'
 subprocess.run(['pdftotext','-layout',str(p),str(L/f'{name}-review.txt')],check=True)
 print(name,'PDF extracted independently')
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name,'keys',list(d))
 for key in ['accepted_count','total_accepted_count','next_global_outcome_number']:print(key,d.get(key))
 print('Accepted titles:',[(x.get('number'),x.get('title')) for x in d.get('accepted',[])])
 print('Excluded/held ids:',[(key,[(x.get('id'),x.get('reason','')) for x in val]) for key,val in d.items() if isinstance(val,list) and key!='accepted' and any(isinstance(x,dict) and 'id' in x for x in val)])
urls=['https://arxiv.org/abs/1911.08613','https://export.arxiv.org/api/query?search_query=all:%22median%20process%22%20AND%20all:majority&start=0&max_results=20','https://export.arxiv.org/api/query?search_query=all:%22majority%20dynamics%22%20AND%20%28all:counterexample%20OR%20all:monotonicity%29&start=0&max_results=20']
records=[]
for i,url in enumerate(urls):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalSourceReview/1.0'}),timeout=18) as r:
   data=r.read(1500000);rec.update(status=r.status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
   (L/f'current-{i}.body').write_bytes(data)
 except Exception as e:rec['failure']=str(e)
 records.append(rec);print(rec)
(L/'current-access.json').write_text(json.dumps(records,indent=2))
