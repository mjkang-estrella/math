from pathlib import Path
import json,hashlib,datetime,shutil
here=Path(__file__).resolve().parent
batch=here.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for lane in ['sol-fresh-source-discovery-r189','root-r189-handback']:
    src=batch/'lanes'/lane
    selected=[p for p in src.iterdir() if p.is_file()]
    if lane.startswith('sol-fresh'):
        selected += [p for p in (src/'primary-copies').iterdir() if p.is_file()]
    for p in sorted(selected):
        dst=here/'copies'/lane/p.relative_to(src)
        dst.parent.mkdir(parents=True,exist_ok=True)
        before=sha(p);shutil.copyfile(p,dst)
        assert before==sha(dst)==sha(p)
        rows.append(dict(original=str(p),copy=str(dst.relative_to(here)),sha256=before))
for name in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
    p=batch/name
    if p.exists():
        dst=here/'administrative'/name;dst.parent.mkdir(exist_ok=True)
        shutil.copyfile(p,dst)
        # Snapshots only; no live bindings for mutable administration.
for label,p in [('ancestor',batch.parents[3]/'AGENTS.md'),('guard',batch/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')]:
    if p.exists():
        dst=here/'administrative'/f'{label}.txt';shutil.copyfile(p,dst)
(here/'freeze-before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_pairs=rows,administration='Snapshots only; no live original hash verification'),indent=2)+'\n')
print('frozen pairs',len(rows))
for name in ['ledger.json','prior-campaign-context.json']:
    d=json.loads((here/'administrative'/name).read_text())
    print(name,'keys',list(d),'accepted',[(x.get('number'),x.get('title')) for x in d.get('accepted',[])])
for name in ['PROOF.md','FAILURES.md','http.jsonl','search-receipt.json']:
    print('\nFILE',name);print((here/'copies/sol-fresh-source-discovery-r189'/name).read_text())
