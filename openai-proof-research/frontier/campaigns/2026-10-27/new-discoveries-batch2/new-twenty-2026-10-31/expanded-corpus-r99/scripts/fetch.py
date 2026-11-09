import urllib.request,urllib.error,json,pathlib,hashlib,datetime,subprocess,concurrent.futures
L=pathlib.Path.cwd()
def fetch(url,name):
 p=L/'sources'/name;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=20) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  p.write_bytes(b);r.update(file=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 (L/'receipts'/ (name+'.json')).write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
if __name__=='__main__':
 import sys
 if sys.argv[1]=='registry':
  for repo in ['openai/math','the-omega-institute/trureturing']:fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',repo.replace('/','-')+'-HEAD.json')
 else:
  rows=json.loads((L/'reservation.json').read_text())['rows']; urls=sorted(set(x['source_url'].replace('/abs/','/pdf/') for x in rows))
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(lambda u:fetch(u,u.rsplit('/',1)[1]+'.pdf'),urls))
