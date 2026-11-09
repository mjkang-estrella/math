import pathlib,requests,hashlib,json,datetime,subprocess,concurrent.futures
w=pathlib.Path(__file__).parent;(w/'sources').mkdir(exist_ok=True)
def fetch(a):
 u='https://arxiv.org/pdf/'+a; r=requests.get(u,timeout=45); p=w/'sources'/ (a+'.pdf'); p.write_bytes(r.content)
 receipt={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'sha256':hashlib.sha256(r.content).hexdigest(),'bytes':len(r.content)}
 if r.status_code==200: subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 return receipt
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,['1605.01888','1608.00747','1608.01158','1607.06122','1607.01215','1605.05667','1606.07474','1606.08485']):
  with (w/'receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
