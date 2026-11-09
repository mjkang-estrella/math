import pathlib,json,urllib.request,urllib.error,hashlib,datetime,resource,concurrent.futures,subprocess,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;S=L/'sources';S.mkdir(exist_ok=True)
def fetch(item):
 name,url=item;p=S/name
 if p.exists():return
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source review'}),timeout=12) as f:
   b=f.read(16000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());p.write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(r,indent=2))
 if p.suffix=='.pdf' and p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=10,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 print(name,r.get('status'),flush=True)
if __name__=='__main__':
 rows=json.loads((L/'literal-records.json').read_text());a=sorted({x['record']['source_url'].rsplit('/',1)[-1] for x in rows.values()})
 items=[(z+ext,'https://arxiv.org/'+kind+'/'+z) for z in a for ext,kind in [('.abs.html','abs'),('.pdf','pdf')]]
 if len(sys.argv)>1:items=json.loads(pathlib.Path(sys.argv[1]).read_text())
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(fetch,items))
