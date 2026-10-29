import urllib.request,hashlib,json,datetime
from pathlib import Path
P=Path(__file__).resolve().parent
urls={
'source-v2.html':'https://arxiv.org/html/2507.07243v2',
'source-abs.html':'https://arxiv.org/abs/2507.07243',
'author-publications.html':'https://jeremymartinmath.github.io/pubs-brief.html',
'omega-foata.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/75fa71fb84c19580a0ea89b3dc7c8158f7aa7446/D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.lean',
'omega-head.html':'https://github.com/the-omega-institute/trureturing',
'followup.html':'https://arxiv.org/html/2508.11587',
}
logs=[]
for name,url in urls.items():
    r={'url':url,'file':name,'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(url,timeout=25) as f:b=f.read(8*1024*1024);r.update(status=f.status,final_url=f.url)
        (P/name).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
    except Exception as e:r['error']=str(e)
    logs.append(r)
(P/'http.json').write_text(json.dumps(logs,indent=2)+'\n')
print(json.dumps(logs,indent=2))
