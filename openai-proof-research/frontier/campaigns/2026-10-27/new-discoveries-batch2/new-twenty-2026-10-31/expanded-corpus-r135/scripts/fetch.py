import urllib.request,urllib.error,json,hashlib,pathlib,datetime,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
items=json.loads((D/'extracted.json').read_text()); receipts=[]
if sys.argv[1]=='heads':
 urls=[(repo.replace('/','-'),'https://api.github.com/repos/'+repo+'/commits/HEAD') for repo in ['openai/math','the-omega-institute/trureturing']]
else: urls=[(i,'https://arxiv.org/pdf/'+o['source_url'].split('/')[-1]) for i,o in items.items()]
for name,url in urls:
 p=D/'sources'/ (name+('.json' if sys.argv[1]=='heads' else '.pdf'))
 if p.exists():continue
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=18) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.write_bytes(b)
  if p.suffix=='.pdf' and b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 receipts.append(r); print(name,r,flush=True)
 (D/'sources'/('receipts-'+sys.argv[1]+'.json')).write_text(json.dumps(receipts,indent=2)+'\n')
