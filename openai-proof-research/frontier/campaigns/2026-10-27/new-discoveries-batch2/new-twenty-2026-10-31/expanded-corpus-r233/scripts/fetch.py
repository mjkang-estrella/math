import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
P=pathlib.Path(__file__).resolve().parents[1]
DENIED={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org','dblp.uni-trier.de'}
for f in (P/'receipts').glob('http-*.json'):
    r=json.loads(f.read_text())
    if r.get('denied'): DENIED.add(urllib.parse.urlparse(r['url']).hostname)
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kw): return None
op=urllib.request.build_opener(NoRedirect)
for url in sys.argv[1:]:
    host=urllib.parse.urlparse(url).hostname
    if host in DENIED: print('SKIP denied',host);continue
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
    name='http-'+stamp; r={'url':url,'utc':stamp}
    try:
        with op.open(urllib.request.Request(url,headers={'User-Agent':'Research audit (public mathematical sources)'}),timeout=25) as h:
            b=h.read(25000000); r.update(status=h.status,headers=dict(h.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
            challenge=any(x in b[:10000].lower() for x in [b'cf-chl-',b'captcha',b'challenge-platform'])
            r['denied']=challenge
            (P/'sources'/(name+'.body')).write_bytes(b)
            r['body']='sources/'+name+'.body'
    except urllib.error.HTTPError as e:
        b=e.read();r.update(status=e.code,headers=dict(e.headers),denied=e.code in (403,429),sha256=hashlib.sha256(b).hexdigest())
        (P/'sources'/(name+'.body')).write_bytes(b);r['body']='sources/'+name+'.body'
    except Exception as e:r.update(error=repr(e))
    if r.get('denied'):DENIED.add(host)
    with (P/'receipts'/(name+'.json')).open('x') as f:json.dump(r,f,indent=2)
    print(url,r.get('status'),r.get('body'),r.get('error',''))
