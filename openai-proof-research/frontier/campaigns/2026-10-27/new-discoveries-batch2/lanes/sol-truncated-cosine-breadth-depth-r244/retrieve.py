from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,sys,subprocess
P=Path(__file__).resolve().parent
def fetch(url,name):
    dst=P/'primary'/name;dst.parent.mkdir(exist_ok=True)
    rec={'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(url,timeout=25) as r:
            raw=r.read(8000000);rec['status']=r.status
        if b'captcha' in raw[:20000].lower() or b'challenge-platform' in raw[:20000].lower():raise RuntimeError('challenge: stop route')
        dst.write_bytes(raw);h=hashlib.sha256(raw).hexdigest();copy=P/'frozen'/name;copy.write_bytes(raw)
        assert hashlib.sha256(dst.read_bytes()).hexdigest()==h==hashlib.sha256(copy.read_bytes()).hexdigest()
        rec.update(original=str(dst),copy=str(copy),sha256=h)
        with (P/'freeze-new.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
        if name.endswith('.pdf'):
            subprocess.run(['pdftotext','-layout',str(copy),str(copy)+'.txt'],check=True)
    except Exception as e:rec['error']=repr(e)
    with (P/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
    print(json.dumps(rec))
if __name__=='__main__':
    if sys.argv[1]=='search':
        fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':sys.argv[2],'max_results':sys.argv[3] if len(sys.argv)>3 else '20','sortBy':'relevance'}),sys.argv[4] if len(sys.argv)>4 else 'search.xml')
    else:
        for ident in sys.argv[1:]:fetch('https://arxiv.org/pdf/'+ident,ident.replace('/','-')+'.pdf')
