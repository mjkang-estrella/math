import pathlib, urllib.request, urllib.error, hashlib, json, datetime, sys,time
D=pathlib.Path(__file__).resolve().parents[1]
receipts=[]; denied=set()
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).netloc in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Guard())
def fetch(url,path):
 host=urllib.parse.urlparse(url).netloc
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(path)}
 if host in denied:r['error']='denied host; skipped';receipts.append(r);return None
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=18) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));path.write_bytes(b)
  receipts.append(r);return b
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   r['status']=e.code
   if e.code in (403,429):denied.add(host)
  receipts.append(r);return None
if __name__=='__main__':
 rows=json.loads((D/'reservation.json').read_text())['rows']
 for row in rows[int(sys.argv[1]):int(sys.argv[2])]:
  aid=row['source_url'].split('/')[-1];fetch('https://arxiv.org/pdf/'+aid,D/'sources'/f'{aid}.pdf')
 (D/'outputs'/f'fetch-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(receipts,indent=2))
