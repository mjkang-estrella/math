"""Evidence acquisition only; all writes confined to I68."""
import json, hashlib, urllib.request, urllib.error, datetime, sys
from pathlib import Path
S=Path(__file__).resolve().parents[2]/'sources/i68_logarithmic_blowup_novelty/primary'
S.mkdir(parents=True,exist_ok=True)
def fetch(name,url):
    rec={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I68 scholarly source audit'}),timeout=35) as r:
            b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
    except urllib.error.HTTPError as e:
        b=e.read();rec.update(status=e.code,error=str(e),headers=dict(e.headers))
    except Exception as e:
        b=b'';rec.update(status=None,error=repr(e))
    out=S/name;out.write_bytes(b);rec.update(file=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
    (S/(name+'.response.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:rec[k] for k in ['name','status','bytes']}),flush=True)
if __name__=='__main__':
    fetch(sys.argv[1],sys.argv[2])
