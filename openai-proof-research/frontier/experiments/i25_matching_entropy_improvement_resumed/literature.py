from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess,re
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i25_matching_entropy_improvement_resumed/literature';S.mkdir(exist_ok=True)
papers=[('gurvits','1106.2844'),('cube-ideal','2505.14497'),('entropy-optimization','1304.8108'),('girth-bethe','2609.02017'),('dong-jain','2609.11049')]
rows=[]
def fetch(name,url,suffix):
    with urllib.request.urlopen(url,timeout=40) as r:b=r.read();final=r.url
    p=S/(name+suffix);p.write_bytes(b);rows.append(dict(name=name,url=url,final_url=final,path=str(p.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return b,p
for name,ident in papers:
    b,p=fetch(name,f'https://arxiv.org/abs/{ident}','-current.html')
    versions=re.findall(re.escape(ident)+r'v(\d+)',b.decode());v=ident+'v'+str(max(map(int,versions)));print(name,v,flush=True)
    fetch(name,f'https://arxiv.org/abs/{v}','-version.html')
    b,p=fetch(name,f'https://arxiv.org/pdf/{v}', '.pdf');q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);bb=q.read_bytes();rows.append(dict(name=name,version=v,path=str(q.relative_to(ROOT)),derived_from=str(p.relative_to(ROOT)),bytes=len(bb),sha256=hashlib.sha256(bb).hexdigest()))
    (S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
