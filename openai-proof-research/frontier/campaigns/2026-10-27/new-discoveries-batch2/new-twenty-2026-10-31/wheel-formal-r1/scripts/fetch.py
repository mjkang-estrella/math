from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,sys
D=Path(__file__).resolve().parent.parent
def get(key,url):
 p=D/'sources'/key
 if p.exists(): return p.read_bytes()
 rec={'url':url,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'wheel-prior-art-research/1.0','Accept':'application/vnd.github+json' if 'api.github' in url else '*/*'}),timeout=30) as r:
   b=r.read(24000000);rec.update(status=r.status,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest());p.write_bytes(b)
 except Exception as e: rec['error']=str(e);b=b''
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(rec,indent=2))
 print(key,rec.get('status',rec.get('error')),len(b),flush=True)
 return b
if __name__=='__main__':
 get(sys.argv[1],sys.argv[2])
