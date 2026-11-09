import urllib.request,urllib.error,json,pathlib,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]
class StopRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in {'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com','palomar'}: raise ValueError('blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def fetch(url,label):
 p=L/'receipts'/label
 if p.with_suffix('.json').exists(): raise ValueError('receipt exists')
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.build_opener(StopRedirect).open(urllib.request.Request(url,headers={'User-Agent':'math-research/1.0'}),timeout=35) as r:
   data=r.read(); rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); p.with_suffix('.body').write_bytes(data)
 except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None))
 p.with_suffix('.json').write_text(json.dumps(rec,indent=2)); print(label,rec.get('status'),rec.get('bytes'),rec.get('error',''),flush=True)
if __name__=='__main__':
 if sys.argv[1]=='sources':
  for row in json.loads((L/'reservation.json').read_text())['rows']: fetch(row['source_url'].replace('/abs/','/html/'),str(row['mathdb_id'])+'-html')
 else: fetch(sys.argv[1],sys.argv[2])
