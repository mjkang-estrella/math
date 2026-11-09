import pathlib,json,urllib.request,urllib.error,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
urls={r['source_url'].replace('/abs/','/pdf/') for r in json.loads((D/'reservation.json').read_text())['rows']}
urls.update('https://api.github.com/repos/'+r+'/commits/HEAD' for r in ['openai/math','the-omega-institute/trureturing'])
receipts=[]
for url in sorted(urls):
 name=url.rsplit('/',1)[-1] if '/pdf/' in url else ('openai' if '/openai/' in url else 'omega')+'-head.json'
 p=D/'sources'/name
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source review'}),timeout=15) as f:
   data=f.read();rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
  if '/pdf/' in url and data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True)
 except Exception as e:rec.update(error=str(e))
 receipts.append(rec);(D/'sources/fetch-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(rec,flush=True)
