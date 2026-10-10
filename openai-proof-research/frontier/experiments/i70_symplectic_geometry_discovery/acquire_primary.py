"""Author-only HTTP acquisition. verify.py replays extract, never HTTP functions."""
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, re, urllib.request, urllib.error
from html.parser import HTMLParser
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i70_symplectic_geometry_discovery/primary'

class Extract(HTMLParser):
    def __init__(self): super().__init__(); self.parts=[]; self.skip=0
    def handle_starttag(self,tag,attrs):
        if tag in ('script','style'): self.skip+=1
        if tag in ('p','div','section','h1','h2','h3','h4','li','br','tr'): self.parts.append('\n')
    def handle_endtag(self,tag):
        if tag in ('script','style'): self.skip-=1
    def handle_data(self,data):
        if not self.skip: self.parts.append(data)
def extract(b):
    p=Extract(); p.feed(b.decode('utf-8',errors='replace'))
    return '\n'.join(s for s in (re.sub(r'\s+',' ',l).strip() for l in ''.join(p.parts).splitlines()) if s)+'\n'
def get(name,url):
    OUT.mkdir(parents=True,exist_ok=True)
    p=OUT/(name+'.body')
    if p.exists(): raise RuntimeError('Refusing refresh: '+name)
    rec=dict(url=url,requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I70 mathematical research source audit'}),timeout=25) as r:
            b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
    except urllib.error.HTTPError as e:
        b=e.read();rec.update(status=e.code,headers=dict(e.headers),failure=str(e))
    except Exception as e:
        b=b'';rec.update(status=None,failure=repr(e))
    p.write_bytes(b);rec.update(body=p.name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
    if rec['status']==200 and ('html' in rec.get('headers',{}).get('Content-Type',rec.get('headers',{}).get('content-type','')) or b.lstrip().startswith((b'<!DOCTYPE',b'<html'))):
        t=extract(b);q=OUT/(name+'.txt');q.write_text(t);rec.update(text=q.name,text_sha256=hashlib.sha256(t.encode()).hexdigest())
    (OUT/(name+'.json')).write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    return rec
def paper(arxiv):
    r=get(arxiv+'-abs','https://arxiv.org/abs/'+arxiv)
    if r['status']!=200:return [r]
    b=(OUT/r['body']).read_text(errors='replace')
    versions=re.findall(re.escape(arxiv)+r'v(\d+)',b)
    if not versions:return [r]
    v=max(map(int,versions)); r2=get(arxiv+f'v{v}-html',f'https://arxiv.org/html/{arxiv}v{v}')
    return [r,r2]
def main():
    ids=['2312.13224','2509.15390','2603.28007','2209.08599','2606.15847','1404.4183']
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
        result=list(ex.map(paper,ids))
    print(json.dumps([[dict(url=r['url'],status=r['status'],bytes=r['bytes']) for r in rs] for rs in result]))
if __name__=='__main__':main()
