from pathlib import Path
import json,hashlib,datetime,urllib.request,urllib.error,sys,re,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=B.parents[3]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
def fetch(n,u):
    assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.'])
    (L/'sources').mkdir(exist_ok=True); rec=dict(utc=now(),url=u,file='sources/'+n)
    try:
        with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Source research (bounded)'}),timeout=25) as f:
            b=f.read(12000001); assert len(b)<12000001
            (L/'sources'/n).write_bytes(b)
            rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
    except Exception as e: rec.update(error=str(e))
    with (L/'http.jsonl').open('a') as f: f.write(json.dumps(rec)+'\n')
    print(rec)
def init():
    records=[]; changes=[]; aliases=json.loads((B/'lanes/sol-fresh-source-discovery-r198/history-aliases.json').read_text()); excluded={x['record']['original'] for x in aliases}
    paths={}
    for n in [198]:
        p=B/f'lanes/sol-fresh-source-discovery-r{n}/scientific-freeze.json'
        for r in json.loads(p.read_text()):
            q=Path(r['original'])
            if str(q) not in excluded and q.suffix.lower()=='.md' and any(x in q.name.lower() for x in ['summary','discovery','proof','review','decision']):paths[str(q)]=r['sha256']
    # New originals: only direct lane reports, never recursively treat copied histories as originals.
    for q in (B/'lanes').glob('*/*.md'):
        if any(x in q.name.lower() for x in ['summary','discovery','proof','review','decision']): paths.setdefault(str(q.resolve()),None)
    for s,old in sorted(paths.items()):
        q=Path(s)
        if not q.is_file():changes.append(dict(original=s,missing=True));continue
        b=q.read_bytes(); h=sha(b); dest='originals/'+str(q.relative_to(R)); (L/dest).parent.mkdir(parents=True,exist_ok=True); (L/dest).write_bytes(b)
        records.append(dict(original=s,copy=dest,sha256=h,previous=old))
        if old and old!=h:changes.append(dict(original=s,old=old,new=h))
    for n in [193,194,197,198]:
        p=B/f'lanes/sol-fresh-source-discovery-r{n}'
        for q in p.glob('*.json'):
            if any(s in q.name for s in ['alias','history-receipt','coverage-receipt']):
                dest=f'index-inputs/r{n}-{q.name}';(L/dest).parent.mkdir(exist_ok=True);bb=q.read_bytes();(L/dest).write_bytes(bb);records.append(dict(original=str(q),copy=dest,sha256=sha(bb)))
    for q in [R/'AGENTS.md',B/'AGENTS.md',*[B/f'lanes/root-r{n}-handback/DECISION.md' for n in [198,197,195,196]]]:
        dest='assigned-inputs/'+str(q.relative_to(R));(L/dest).parent.mkdir(parents=True,exist_ok=True);bb=q.read_bytes();(L/dest).write_bytes(bb);records.append(dict(original=str(q),copy=dest,sha256=sha(bb)))
    for n in ['NEXT.md','ledger.json','prior-campaign-context.json']:
        q=B/n
        if q.exists():(L/('snapshot-'+n)).write_bytes(q.read_bytes())
    save('scientific-freeze.json',records);save('changed-originals.json',changes)
    save('coverage-receipt.json',dict(utc=now(),records=len(records),aliases_excluded=len(excluded),rule='Reuse r193/r194/r197/r198 indexes; r198 provenance-qualified copied aliases excluded; only direct new lane reports added. No equal-byte-only provenance inference.',limits='Bounded original-record screen, not all history; parked intervals not reopened. Active reports are explicit point-in-time snapshots. Old changed bytes remain in predecessor lane freeze, not overwritten.'))
    print('frozen',len(records),'changed',len(changes))
def screen(pattern,name):
    hits=[]
    for r in json.loads((L/'scientific-freeze.json').read_text()):
        if not r['copy'].startswith('originals/'): continue
        t=(L/r['copy']).read_text(errors='replace'); ms=list(re.finditer(pattern,t,re.I))
        if ms:hits.append(dict(original=r['original'],sha256=r['sha256'],excerpts=[t[max(0,m.start()-100):m.end()+160] for m in ms[:8]]))
    save(name,dict(utc=now(),pattern=pattern,hits=hits));print('hits',len(hits));print(json.dumps(hits[:10],indent=2))
if __name__=='__main__':
    if sys.argv[1]=='init':init()
    elif sys.argv[1]=='screen':screen(sys.argv[2],sys.argv[3])
    else:
        for a in sys.argv[1:]:fetch(*a.split('=',1))
