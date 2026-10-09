from pathlib import Path
import urllib.request,hashlib,json,datetime,concurrent.futures
from html.parser import HTMLParser
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i17_six_point_ramsey_novelty_r3/literature'
class Text(HTMLParser):
    def __init__(self): super().__init__(); self.out=[]; self.skip=0
    def handle_starttag(self,t,a):
        if t in ('script','style'):self.skip+=1
        if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.out.append('\n')
    def handle_endtag(self,t):
        if t in ('script','style'):self.skip-=1
        if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.out.append('\n')
    def handle_data(self,d):
        if not self.skip:self.out.append(d)
def run():
    S.mkdir(parents=True,exist_ok=True)
    refs=['2609.23327','2608.09649','2608.11736','2606.13472','2510.15677','1012.5468','1212.1803','2608.10865']
    urls=[('arxiv-'+r+'-abs','https://arxiv.org/abs/'+r) for r in refs]
    urls += [('arxiv-'+r+'-html','https://arxiv.org/html/'+r) for r in refs]
    urls += [('upstream-current-commit','https://api.github.com/repos/openai/math/commits/main')]
    def fetch(pair):
        name,url=pair; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
        try:
            with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source comparison'}),timeout=45) as r:b=r.read(); final=r.url; ct=r.headers.get('Content-Type','')
            ext='.json' if 'json' in ct else '.html';p=S/(name+ext);p.write_bytes(b)
            out={'url':url,'final_url':final,'retrieved_utc':now,'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'content_type':ct}
            if ext=='.html':
                parser=Text();parser.feed(b.decode(errors='replace'));t='\n'.join(x.strip() for x in ''.join(parser.out).splitlines() if x.strip())+'\n';tp=S/(name+'.txt');tp.write_text(t);out['text_path']=str(tp.relative_to(ROOT));out['text_sha256']=hashlib.sha256(tp.read_bytes()).hexdigest()
            return out
        except Exception as e:return {'url':url,'retrieved_utc':now,'error':str(e)}
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:out=list(pool.map(fetch,urls))
    (S/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in x.items() if k in ('url','bytes','error')} for x in out],indent=2))
if __name__=='__main__':run()
