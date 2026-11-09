import pathlib, hashlib, json, shutil
HERE=pathlib.Path(__file__).resolve().parent
B=HERE.parent.parent
rows=[]
def save(p,category):
    p=p.resolve(); data=p.read_bytes(); h=hashlib.sha256(data).hexdigest()
    q=HERE/category/p.relative_to(B); q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(data)
    assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
    rows.append(dict(original=str(p),copy=str(q.relative_to(HERE)),sha256=h,size=len(data)))
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']: save(B/n,'administrative')
for lane in ['sol-floor-sums-source-formal-r1','sol-floor-sums-certificate-r2','sol-floor-sums-certificate-preliminary-review-r1','sol-floor-sums-source-prior-review-r2']:
    d=B/'lanes'/lane
    for p in sorted(d.iterdir()):
        if p.is_file() and p.suffix in ['.md','.py','.json','.jsonl','.lean','.sh','.gz']: save(p,'frozen')
    # Freeze original direct primary inputs, never historical nested snapshots.
    if lane=='sol-floor-sums-certificate-r2':
        for p in sorted((d/'frozen').iterdir()):
            if p.is_file(): save(p,'frozen')
(HERE/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print('frozen',len(rows),'files')
