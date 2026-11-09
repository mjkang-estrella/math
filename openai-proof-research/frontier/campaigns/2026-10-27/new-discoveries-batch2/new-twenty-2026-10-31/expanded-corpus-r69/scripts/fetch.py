import pathlib,json,urllib.request,datetime,hashlib,concurrent.futures,sys
P=pathlib.Path(__file__).resolve().parents[1]
def get(item):
 name,url=item;dest=P/'sources'/name;rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(dest)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source review'}),timeout=16) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));dest.write_bytes(data)
 except Exception as e:rec['error']=str(e)
 (P/'receipts'/f'{name}.json').write_text(json.dumps(rec,indent=2)+'\n');return rec
if __name__=='__main__':
 if sys.argv[1]=='registry':items=[('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
 else:
  rows=json.loads((P/'outputs/extracted.json').read_text());ars=sorted(set(x['record']['source_url'].rsplit('/',1)[-1] for x in rows.values()));a,b=map(int,sys.argv[1:]);items=[(x+'.html','https://arxiv.org/html/'+x) for x in ars[a:b]]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
  for x in e.map(get,items):print(json.dumps(x))
