from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
records=[]
def freeze(p,admin=False):
    p=Path(p); data=p.read_bytes(); h=hashlib.sha256(data).hexdigest()
    d=L/('administrative' if admin else 'frozen')/(p.parent.name+'--'+p.name)
    d.parent.mkdir(parents=True,exist_ok=True); d.write_bytes(data)
    assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(d.read_bytes()).hexdigest()
    records.append(dict(original=str(p),copy=str(d),sha256=h,administrative=admin))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:freeze(B/name,True)
freeze(R/'AGENTS.md',True)
for lane in ['sol-two-defect-coloring-breadth-depth-r255','sol-wide-analytic-source-scout-r254','sol-spectral-energy-breadth-depth-r253']:
    for n in ['SUMMARY.md','SCOUTING.md','discovery.md']:
        p=B/'lanes'/lane/n
        if p.exists():freeze(p)
for n in ['upstream.json','CONTENTS.md','preprints-tree.json']:
    freeze(R/'sources'/n)
(L/'bindings.json').write_text(json.dumps(records,indent=2))
print('Frozen',len(records),'files',datetime.datetime.now(datetime.timezone.utc).isoformat())
for r in records:
    p=Path(r['copy'])
    if p.suffix=='.md' and 'SCOUTING' not in p.name:print(p.name,p.read_text()[:5500])
print('ADMIN TITLES')
for n in ['ledger.json','prior-campaign-context.json']:
    j=json.loads((L/'administrative'/('new-discoveries-batch2--'+n)).read_text())
    print(n,[(x.get('number'),x.get('title')) for x in j.get('accepted',[])])
