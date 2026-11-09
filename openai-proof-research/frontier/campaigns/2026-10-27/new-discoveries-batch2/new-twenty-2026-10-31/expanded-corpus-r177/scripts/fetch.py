import pathlib,urllib.request,urllib.error,json,datetime,hashlib,sys,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1]
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
denied=set(json.loads((D/'outputs/denied.json').read_text())) if (D/'outputs/denied.json').exists() else set()
# inherited denied hosts/routes are never used
opener=urllib.request.build_opener(Guard())
def get(key,url):
 host=urllib.parse.urlparse(url).hostname
 if host in denied:return {'url':url,'error':'host already denied'}
 now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'Research verification contact not required'}),timeout=18) as r: data=r.read(); status=r.status; final=r.url
  (D/'sources'/key).write_bytes(data); rec=dict(url=url,final_url=final,status=status,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path='sources/'+key)
 except Exception as e:
  rec=dict(url=url,utc=now,error=str(e))
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):denied.add(host)
 (D/'sources'/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');(D/'outputs/denied.json').write_text(json.dumps(sorted(denied)))
 print(key,rec.get('status',rec.get('error')),flush=True);return rec
if __name__=='__main__':
 todo=json.loads((D/sys.argv[1]).read_text())
 for key,url in todo:get(key,url)
