import json,sys,time,urllib.request,urllib.parse,urllib.error,datetime,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parents[1]; out=L/'outputs/github-search.json'
res=json.loads(out.read_text()) if out.exists() else []
for q in sys.argv[1:]:
    url='https://api.github.com/search/repositories?q='+urllib.parse.quote(q)+'&per_page=20'
    rec={'query':q,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-prior-art-screen','Accept':'application/vnd.github+json'}),timeout=20) as r:
            b=r.read(); d=json.loads(b); rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),total_count=d.get('total_count'),
              hits=[{'full_name':i['full_name'],'description':(i.get('description') or '')[:160],'html_url':i['html_url'],'pushed_at':i.get('pushed_at')} for i in d.get('items',[])])
    except urllib.error.HTTPError as e:
        rec.update(status=e.code,error=str(e)[:200])
    except Exception as e:
        rec.update(error=repr(e)[:200])
    res.append(rec); out.write_text(json.dumps(res,indent=1))
    print(q,'|',rec.get('status'),rec.get('total_count'),[h['full_name'] for h in rec.get('hits',[])][:8],flush=True)
    if rec.get('status') in (403,429): print('STOP: denied'); break
    time.sleep(7)
