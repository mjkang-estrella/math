from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,shutil,subprocess
L=Path(__file__).resolve().parent;D=L/'retrieved';D.mkdir(exist_ok=True)
urls={
 'current.xml':'https://export.arxiv.org/api/query?id_list=1807.11899,1010.4009,1102.3698,1803.00292,1810.03533',
 'durand-current.pdf':'https://arxiv.org/pdf/1010.4009',
 'target-search.xml':'https://export.arxiv.org/api/query?search_query=all:%22inverse+period-doubling%22&start=0&max_results=15',
}
rows=[]
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-review/1.0'}),timeout=25) as r:
   data=r.read(8_000_001);assert len(data)<=8_000_000
   row.update(status=r.status,final_url=r.url,bytes=len(data))
  (D/name).write_bytes(data)
  q=L/'frozen-current'/name;q.parent.mkdir(exist_ok=True);shutil.copyfile(D/name,q)
  digest=hashlib.sha256(data).hexdigest();assert digest==hashlib.sha256(q.read_bytes()).hexdigest()
  row['sha256']=digest
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(q),str(q.with_suffix('.txt'))],check=True)
 except Exception as e:row['failure']=repr(e)
 rows.append(row)
(L/'current-retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
