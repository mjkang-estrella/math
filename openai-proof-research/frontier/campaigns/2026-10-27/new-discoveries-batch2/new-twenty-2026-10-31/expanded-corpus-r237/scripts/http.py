from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
L=Path(__file__).resolve().parents[1]; S=L/'sources'
def get(key,url):
 p=S/key
 if p.exists() or p.with_suffix(p.suffix+'.receipt.json').exists():raise RuntimeError('Never overwrite receipts')
 denied=set(json.loads((S/'denied.json').read_text())) if (S/'denied.json').exists() else set()
 class Guard(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urllib.parse.urlparse(url).hostname in denied:rec['error']='host denied; not requested'
 else:
  try:
   with urllib.request.build_opener(Guard()).open(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=20) as r:
    data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
   if b'cf-chl-' in data or b'Just a moment...' in data[:2000]:denied.add(urllib.parse.urlparse(r.url).hostname);rec['challenge']=True
  except urllib.error.HTTPError as e:
   data=e.read();p.write_bytes(data);rec.update(status=e.code,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
   if e.code in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
  except Exception as e:rec['error']=str(e)
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(rec,indent=2));(S/'denied.json').write_text(json.dumps(sorted(denied)))
 print(key,rec.get('status',rec.get('error')),flush=True);return rec
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  R=json.loads((L/'reservation.json').read_text());seen=set()
  for r in R['rows']:
   a=r['source_url'].rsplit('/',1)[-1]
   if a in seen:continue
   seen.add(a);get(a+'.abs.html',r['source_url']);get(a+'.pdf','https://arxiv.org/pdf/'+a)
