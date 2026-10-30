from pathlib import Path
import json,hashlib,datetime,urllib.request,sys,subprocess
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def get(name,url):
    (L/'sources').mkdir(exist_ok=True); (L/'primary').mkdir(exist_ok=True)
    r={'utc':utc(),'url':url,'name':name}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research/1.0'}),timeout=35) as f:
            data=f.read(12000001); assert len(data)<=12000000
            r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
        p=L/'sources'/name;p.write_bytes(data);q=L/'primary'/name;q.write_bytes(data)
        r.update(sha256=sha(p),bytes=len(data),original=str(p),copy=str(q)); assert sha(q)==r['sha256']
    except Exception as e:r['error']=repr(e)
    with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
    print(json.dumps(r))
if sys.argv[1]=='get':get(sys.argv[2],sys.argv[3])
if sys.argv[1]=='init':
    (L/'administrative').mkdir(exist_ok=True);(L/'changed').mkdir(exist_ok=True)
    for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
        p=B/n
        if p.exists():(L/'administrative'/n).write_bytes(p.read_bytes())
    records={};refs=[]
    for n,fn in [(207,'qualified-original-index.json'),(208,'history-refresh.json')]:
        p=L.parent/f'sol-fresh-source-discovery-r{n}'/fn
        x=json.loads(p.read_text());print(n,str(x)[:1300]);
        (L/'administrative'/f'r{n}-{fn}').write_bytes(p.read_bytes());refs.append({'path':str(p),'sha256':sha(p)})
        rows=x.get('records',x.get('qualified',[]))
        for r in rows:
            if 'original' in r:records[r['original']]=r
    print('records',len(records))
    for d in L.parent.iterdir():
        if d.is_dir() and d!=L:
            for p in d.iterdir():
                if p.is_file() and p.suffix=='.md' and (p.name in ['SUMMARY.md','discovery.md','REPORT.md','report.md','review.md','FINDINGS.md'] or 'DECISION' in p.name):records.setdefault(str(p),{'original':str(p)})
    out=[]
    for i,(s,r) in enumerate(sorted(records.items())):
        p=Path(s)
        if not p.exists():out.append(dict(r,missing=True));continue
        h=sha(p);ref=r.get('snapshot_reference',r.get('snapshot',r.get('copy')))
        if ref and not Path(ref).is_absolute():ref=str(L.parent/'sol-fresh-source-discovery-r208'/ref)
        if h!=r.get('sha256') or not ref or not Path(ref).exists() or sha(ref)!=h:
            q=L/'changed'/f'{i:04d}-{p.name}';q.write_bytes(p.read_bytes());ref=str(q)
        out.append({'original':s,'sha256':h,'snapshot_reference':ref,'snapshot_verified':sha(ref)==h})
    save('history.json',{'utc':utc(),'records':out,'canonical_indexes':refs,'qualification':'Original-path inherited index and immediate top-level reports; not an all-history clearance. Snapshots only.'})
    print('history',len(out),'changed',len(list((L/'changed').iterdir())))
if sys.argv[1]=='screen':
    terms=sys.argv[2:];hits=[]
    for r in json.loads((L/'history.json').read_text())['records']:
        if r.get('missing'):continue
        t=Path(r['snapshot_reference']).read_text(errors='replace').lower()
        hit=[a for a in terms if a.lower() in t]
        if hit:hits.append({'original':r['original'],'terms':hit})
    save('screen-'+hashlib.sha256('|'.join(terms).encode()).hexdigest()[:8]+'.json',{'utc':utc(),'terms':terms,'hits':hits});print(json.dumps(hits,indent=2))
