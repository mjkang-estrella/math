import json,sys,time,urllib.request,urllib.parse,hashlib,datetime,pathlib
L=pathlib.Path(__file__).resolve().parents[1]; out=[]
for q in sys.argv[1:]:
    url='https://api.github.com/search/repositories?q='+urllib.parse.quote(q)
    rec=dict(query=q,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-screen','Accept':'application/vnd.github+json'}),timeout=20) as s:
            d=json.loads(s.read()); rec.update(status=s.status,total=d.get('total_count'),hits=[(i['full_name'],i.get('description')) for i in d.get('items',[])[:10]])
    except Exception as e:
        rec['error']=repr(e)[:200]
        if '403' in rec['error'] or '429' in rec['error']: out.append(rec); print(json.dumps(rec)); break
    out.append(rec); print(json.dumps(rec)[:400],flush=True); time.sleep(9)
p=L/'outputs/github-search.json'; prev=json.loads(p.read_text()) if p.exists() else []
p.write_text(json.dumps(prev+out,indent=1))
