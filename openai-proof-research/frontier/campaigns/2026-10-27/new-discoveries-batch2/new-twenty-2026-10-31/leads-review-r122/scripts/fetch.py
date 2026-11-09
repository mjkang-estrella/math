import urllib.request,sys,json,hashlib,datetime
from pathlib import Path
for arg in sys.argv[1:]:
    name,url=arg.split('=',1);p=Path('sources')/name
    receipt=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical literature review'}),timeout=18) as r:
            data=r.read(18000000);receipt.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());p.write_bytes(data)
    except Exception as e:receipt['error']=str(e)
    p.with_name(p.name+'.receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt),flush=True)
