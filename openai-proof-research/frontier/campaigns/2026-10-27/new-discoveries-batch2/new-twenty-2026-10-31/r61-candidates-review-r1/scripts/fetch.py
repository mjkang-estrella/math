# Single lawful HTTP GET with dated receipt. Usage: fetch.py key url. No retries.
import sys,pathlib,json,hashlib,datetime,urllib.request,urllib.error
L=pathlib.Path(__file__).resolve().parents[1]
key,url=sys.argv[1],sys.argv[2]; p=L/'sources'/key
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification (single request, no retries)'}),timeout=25) as r:
        data=r.read(); rec=dict(url=url,final_url=r.url,status=r.status,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
    p.write_bytes(data)
except urllib.error.HTTPError as e:
    rec=dict(url=url,utc=now,status=e.code,error=str(e))
except Exception as e:
    rec=dict(url=url,utc=now,error=repr(e))
(L/'sources'/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(key,rec.get('status'),rec.get('bytes'),rec.get('error',''))
