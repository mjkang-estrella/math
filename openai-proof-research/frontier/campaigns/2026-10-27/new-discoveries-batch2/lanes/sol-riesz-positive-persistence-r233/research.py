import pathlib, hashlib, json, shutil, sys, subprocess, urllib.request, datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(p, administrative=False):
    p=pathlib.Path(p); h=sha(p)
    dest=L/('administrative' if administrative else 'frozen')/(h[:16]+'-'+p.name)
    dest.parent.mkdir(exist_ok=True)
    if not dest.exists(): shutil.copyfile(p,dest)
    assert sha(p)==h==sha(dest)
    with (L/'provenance.jsonl').open('a') as f: f.write(json.dumps({'original':str(p),'copy':str(dest),'sha256':h,'administrative':administrative})+'\n')
    return dest
if sys.argv[1]=='bootstrap':
    for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
        if p.exists(): freeze(p,True)
    for name in ['sol-wavelet-annulus-breadth-depth-r230']:
        for fn in ['SUMMARY.md','SCOUTING.md','discovery.json','progress.json']:
            p=B/'lanes'/name/fn
            if p.exists():
                q=freeze(p); print(str(q)); print(q.read_text()[:38000])
    matches=[]
    indexed=subprocess.run(['rg','-l','-i','Riesz|Bilyk|Grabner|2410.22104|2504.04845',str(B/'lanes'),'-g','SUMMARY.md','-g','discovery.json'],capture_output=True,text=True).stdout.splitlines()
    (L/'alias-path-index.txt').write_text('\n'.join(indexed))
    for p in sorted(set(pathlib.Path(x).parent for x in indexed)):
        if p.is_dir() and p!=L:
            for fn in ['SUMMARY.md','discovery.json']:
                q=p/fn
                if q.exists():
                    # Freeze before scientific reading; compact files only, never trees.
                    if q.stat().st_size<120000:
                        r=freeze(q)
                        s=r.read_text(errors='replace')
                        if any(x.lower() in s.lower() for x in ['Riesz','Bilyk','Grabner','2410.22104','2504.04845']): matches.append({'path':str(q),'copy':str(r),'excerpts':[s[max(0,i-120):i+600] for x in ['Riesz','Bilyk','Grabner','2410.22104','2504.04845'] if (i:=s.lower().find(x.lower()))>=0]})
    (L/'alias-scan.json').write_text(json.dumps(matches,indent=2)); print(json.dumps(matches)[:18000])
if sys.argv[1]=='sources':
    P=B/'lanes/sol-wavelet-annulus-breadth-depth-r230/primary'
    for fn in ['grabner.pdf','grabner.txt','2504.04845v1.pdf','2504.04845v1.txt','2511.18217v1.pdf','2511.18217v1.txt','2512.17285v1.pdf','2512.17285v1.txt']:
        q=freeze(P/fn)
        if fn.endswith('.txt'):
            s=q.read_text(); print('\nSOURCE',fn)
            if fn=='grabner.txt':
                for term in ['Theorem 8.','Remark 6.','Remark 7.','equivalent','Theorem 1.','Theorem 4.']:
                    for i in [i for i in range(len(s)) if s.startswith(term,i)][:5]: print(s[max(0,i-500):i+6500])
            elif fn=='2504.04845v1.txt':
                i=s.find('Question 5.1');print(s[max(0,i-4000):i+3000])
            else: print(s[:5500]); print('\nQUESTION INDEX\n'+'\n'.join(x for x in s.splitlines() if any(t in x for t in ['Problem','Question','Conjecture']))[:15000])
if sys.argv[1]=='more':
    P=B/'lanes/sol-wavelet-annulus-breadth-depth-r230/primary'
    for fn in ['2510.11908v2.pdf','2510.11908v2.txt']:
        q=freeze(P/fn)
        if fn.endswith('.txt'): print(q.read_text()[6000:43000])
    s=next((L/'frozen').glob('*-2504.04845v1.txt')).read_text()
    print('UP24 remaining',s[42000:])
if sys.argv[1]=='live':
    import urllib.parse
    urls=[('bilyk-latest.html','https://arxiv.org/abs/2410.22104'),('up24-latest.html','https://arxiv.org/abs/2504.04845'),('current-riesz.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'all:"Riesz" AND (au:Grabner OR au:Bilyk)','start':0,'max_results':20,'sortBy':'submittedDate','sortOrder':'descending'})),('registry.html','https://mathdb.org')]
    (L/'primary').mkdir(exist_ok=True)
    for fn,url in urls:
        row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
        try:
            with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=22) as r:
                data=r.read(2500000);row.update(status=r.status,final_url=r.url)
            q=L/'primary'/fn;q.write_bytes(data);row.update(bytes=len(data),sha256=sha(q)); frozen=freeze(q)
            print(fn, data.decode(errors='replace')[:1800])
        except Exception as e: row.update(error=str(e));print(row)
        with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
if sys.argv[1]=='read':
    name,term=sys.argv[2:4];q=next((L/'frozen').glob('*-'+name));s=q.read_text();i=s.find(term);print(s[max(0,i-700):i+int(sys.argv[4])])
if sys.argv[1]=='nearest':
    url='https://arxiv.org/pdf/2409.16508v1';row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(url,timeout=25) as r: data=r.read(3000000);row['status']=r.status
        p=L/'primary/2409.16508v1.pdf';p.write_bytes(data);q=freeze(p);row['sha256']=sha(p)
    except Exception as e:row['error']=str(e)
    with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
    bindings=[]
    for q in (L/'frozen').glob('*.pdf'):
        dest=L/'primary'/(q.name+'.txt');subprocess.run(['pdftotext','-layout',str(q),str(dest)],check=True)
        z=freeze(dest);bindings.append({'pdf':str(q),'pdf_sha256':sha(q),'text':str(z),'text_sha256':sha(z),'command':['pdftotext','-layout',str(q),str(dest)]})
        if '2409.' in q.name:
            s=z.read_text();print(s[:8000]);print('\n'.join(s[max(0,m.start()-100):m.start()+1300] for m in __import__('re').finditer('Theorem [1-9]|Conjecture',s))[:18000])
    (L/'text-bindings.json').write_text(json.dumps(bindings,indent=2))
