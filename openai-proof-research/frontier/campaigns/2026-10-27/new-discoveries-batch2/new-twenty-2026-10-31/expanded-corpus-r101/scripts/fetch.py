import pathlib,json,urllib.request,urllib.error,datetime,hashlib,concurrent.futures,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(item):
 name,url=item; p=D/'sources'/name
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.write_bytes(b)
 except Exception as e:r.update(error=str(e))
 (D/'receipts'/f'{name}.json').write_text(json.dumps(r,indent=2)+'\n');return name,r
if __name__=='__main__':
 x=json.loads((D/'extracted.json').read_text()); items=[(i+'.pdf',o['source_url'].replace('/abs/','/pdf/')) for i,o in x.items()]
 items += [(repo.split('/')[-1]+'-HEAD.json','https://api.github.com/repos/'+repo+'/commits/HEAD') for repo in ['openai/math','the-omega-institute/trureturing']]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for name,r in pool.map(fetch,items):
   print(name,r,flush=True)
   if name.endswith('.pdf') and 'sha256' in r:
    subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/'sources'/name.replace('.pdf','.txt'))],check=False)
