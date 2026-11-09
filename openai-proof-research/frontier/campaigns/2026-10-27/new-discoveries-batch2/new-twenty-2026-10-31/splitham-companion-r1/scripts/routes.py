from pathlib import Path
import urllib.request,urllib.error,json,time
routes=[('citing-2024','https://api.openalex.org/works/W4400848169'),('citing-fan','https://api.openalex.org/works/W7164133400'),('citing-spectral','https://api.openalex.org/works/W7214296171'),('arxiv-listing','https://arxiv.org/search/?query=Song+Zhan+Liu+split&searchtype=all&abstracts=show&order=-announced_date_first&size=50')]
receipts=[]
for label,url in routes:
    p=Path('downloads')/label;p.mkdir(exist_ok=False)
    rec=dict(label=label,url=url,started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Focused mathematics literature comparison'}),timeout=20) as f:
            rec.update(status=f.status,final_url=f.url,headers=dict(f.headers));data=f.read(8*1024*1024);(p/'body').write_bytes(data);rec['bytes']=len(data)
    except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
    (p/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');receipts.append(rec)
    print(json.dumps(rec),flush=True)
Path('outputs/http-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
