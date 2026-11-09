from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((L/'freeze.json').read_text())
out=[]
for r in f['bindings']:
    p=Path(r['copy']); assert sha(p)==r['sha256']
    q={'path':str(p),'expected':r['sha256'],'after':sha(p),'kind':r['kind']}
    if r['kind'].startswith('scientific'):
        assert sha(Path(r['original']))==r['sha256']
        q['original']=r['original'];q['original_after']=sha(Path(r['original']))
    out.append(q)
for r in json.loads((L/'references.json').read_text()):
    assert sha(Path(r['path']))==r['sha256']
    out.append(dict(r,after=sha(Path(r['path']))))
for p in (L/'retrieval').glob('*.freeze.json'):
    r=json.loads(p.read_text());pdf=p.with_name(p.name.replace('.freeze.json','.pdf'))
    if pdf.exists(): assert sha(pdf)==r['sha256']
(L/'before-after.json').write_text(json.dumps(out,indent=2)+'\n')
entries=[{'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'final-manifest.json','verification-receipt.json'}]
(L/'final-manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excludes':['final-manifest.json','verification-receipt.json'],'files':entries},indent=2)+'\n')
print('manifest written',len(entries))
