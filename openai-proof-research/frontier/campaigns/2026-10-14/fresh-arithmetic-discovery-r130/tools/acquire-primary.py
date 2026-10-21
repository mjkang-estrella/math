from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r130')
items=[('laurent2000','https://publi.math.unideb.hu/paper/599/download/10_5486_PMD_2000_2310.pdf'),('meiburg2022v1','https://arxiv.org/pdf/2208.13356v1'),('alekseyev2011v1','https://arxiv.org/pdf/1104.5100v1')]
def get(x):
    name,url=x
    try:
        with urllib.request.urlopen(url,timeout=45) as q:b=q.read();final=q.url;headers=dict(q.headers)
        assert b.startswith(b'%PDF'),b[:60]
        dest=R/'private/primary'/(name+'.pdf');dest.write_bytes(b)
        subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],check=True)
        return {'name':name,'url':url,'final_url':final,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'headers':headers,'status':'acquired'}
    except Exception as e:return {'name':name,'url':url,'status':'failed','error':repr(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as p:out=list(p.map(get,items))
(R/'private/primary/acquisition.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k!='headers'} for x in out],indent=2))
