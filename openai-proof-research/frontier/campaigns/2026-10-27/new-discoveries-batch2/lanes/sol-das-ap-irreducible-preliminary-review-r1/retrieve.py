"""Bounded lawful requests, no retries; freeze response before scientific reading."""
import urllib.request,urllib.error,json,hashlib,datetime,shutil
from pathlib import Path
root=Path(__file__).parent
def get(name,url):
    (root/'retrieval/original').mkdir(parents=True,exist_ok=True)
    (root/'retrieval/frozen').mkdir(parents=True,exist_ok=True)
    rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as r:
            data=r.read(24*1024*1024+1);assert len(data)<=24*1024*1024
            rec.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
    except urllib.error.HTTPError as e:
        data=e.read(100000);rec.update(status=e.code,error=str(e),terminal=True)
    except Exception as e:
        data=b'';rec.update(error=repr(e),terminal=True)
    a=root/'retrieval/original'/name;b=root/'retrieval/frozen'/name
    a.write_bytes(data);shutil.copyfile(a,b)
    h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    assert h(a)==h(b);rec.update(sha256=h(a),bytes=len(data))
    with (root/'retrieval/http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
    print(json.dumps(rec))
if __name__=='__main__':
    get('current-arxiv.xml','https://export.arxiv.org/api/query?search_query=all:%22algebraic%20positivity%22&start=0&max_results=35&sortBy=lastUpdatedDate&sortOrder=descending')
    get('ela-metadata.json','https://api.crossref.org/works?query.title=On%20sign%20pattern%20matrices%20that%20allow%20or%20require%20algebraic%20positivity&rows=2')
    get('das-citations.json','https://api.semanticscholar.org/graph/v1/paper/ARXIV:2112.00442/citations?fields=title,year,openAccessPdf,externalIds&limit=100')
