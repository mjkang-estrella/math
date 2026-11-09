import pathlib,json,hashlib,datetime,urllib.request,subprocess,concurrent.futures,os
L=pathlib.Path(__file__).resolve().parents[1]; P=L.parent; B=P.parent
d=json.loads((L/'extracted.json').read_text())
for i,r in d.items():r['statement_sha256']=hashlib.sha256(r['row']['statement'].encode()).hexdigest()
(L/'extracted.json').write_text(json.dumps(d,indent=2))
# Narrow textual historical screen, preserve exact matches, no corpus/raw numeric haystacks.
ids='|'.join(d)
r=subprocess.run(['rg','-n','-g','*.md','-g','results.json','-g','review.json','-g','ledger.json','-g','!expanded-corpus-r111/**',ids,str(B)],capture_output=True,text=True)
(L/'history-matches.txt').write_text(r.stdout)
def fetch(item):
 name,url=item; target=L/'sources'/name; receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source review'}),timeout=28) as f:
   data=f.read();receipt.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());target.write_bytes(data)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(target),str(target.with_suffix('.txt'))],capture_output=True,timeout=15)
 except Exception as e:receipt.update(error=str(e))
 return name,receipt
items=[]
for i,r in d.items():
 cached=P/'expanded-corpus-r107/sources'/f'{i}.pdf'
 items.append((f'{i}.pdf',r['row']['source_url'].replace('/abs/','/pdf/')))
items += [('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 receipts=dict(ex.map(fetch,items))
(L/'sources/receipts.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
