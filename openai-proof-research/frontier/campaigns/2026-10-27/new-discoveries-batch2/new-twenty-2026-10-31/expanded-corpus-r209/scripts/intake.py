import json,hashlib,sys
from pathlib import Path
L=Path(sys.argv[1]).resolve(); B=L.parent.parent
R=json.loads((L/'reservation.json').read_text()); ids=set(r['mathdb_id'] for r in R['rows']); out={}
h=lambda x:hashlib.sha256(x).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    chunkhash=h(p.read_bytes())
    for n,line in enumerate(p.open('rb'),1):
        if not any(str(i).encode() in line for i in ids): continue
        d=json.loads(line); i=d.get('mathdb_id',d.get('id'))
        if i in ids:
            (L/f'raw/{i}.jsonl').write_bytes(line)
            st=d.get('statement') or d.get('statement_text') or ''
            out[str(i)]={'chunk':p.name,'line':n,'chunk_sha256':chunkhash,'raw_sha256':h(line),'statement_sha256':h(st.encode()) if isinstance(st,str) else None,'record':d}
(L/'outputs/exact-records.json').write_text(json.dumps(out,indent=2))
print(len(out), sorted(out))
print(list(next(iter(out.values()))['record'].keys()))
