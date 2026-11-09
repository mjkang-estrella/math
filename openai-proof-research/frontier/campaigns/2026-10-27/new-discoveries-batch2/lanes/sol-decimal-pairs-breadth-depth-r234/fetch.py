from pathlib import Path
import sys,json,hashlib,urllib.request,datetime,subprocess
L=Path(__file__).resolve().parent
def fetch(name,url):
    rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
    p=L/'sources'/name
    if p.exists(): raise ValueError('immutable target exists: '+name)
    try:
        with urllib.request.urlopen(url,timeout=25) as r:
            d=r.read(8000001)
            if len(d)>8000000: raise ValueError('body exceeds 8MB bound')
            rec.update(status=r.status,headers=dict(r.headers),sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
        p.write_bytes(d)
        assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['sha256']
        if name.endswith('.pdf'):
            subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
            rec['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
    except Exception as e: rec['failure']=str(e)
    with (L/'retrieval-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
    print(name,rec.get('status'),rec.get('failure',''))
if __name__=='__main__':
    for name,url in json.loads(sys.argv[1]):fetch(name,url)
