exec(open(__file__.replace('extra_fetch.py','fetch.py')).read().split('urls=')[0])
urls={'kinetic':'https://arxiv.org/pdf/1907.07266','tree':'https://arxiv.org/pdf/1907.11328','known-egz':'https://www.aimspress.com/aimspress-data/math/2023/3/PDF/math-08-03-338.pdf'}
receipts=[]
for key,url in urls.items():
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(url,timeout=25);data=r.content;p=L/'sources'/(key+('.pdf' if data.startswith(b'%PDF') else '.response'));p.write_bytes(data);receipts.append(dict(key=key,url=url,final_url=r.url,utc=t,status=r.status_code,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p)))
 except Exception as e:receipts.append(dict(key=key,url=url,utc=t,error=str(e)))
 print(receipts[-1],flush=True)
 (L/'extra-source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
