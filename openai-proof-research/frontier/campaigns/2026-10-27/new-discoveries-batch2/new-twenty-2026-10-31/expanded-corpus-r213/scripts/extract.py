import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]
ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    matches=[]
    with p.open('rb') as f:
        for i,raw in enumerate(f,1):
            # parse only lines containing reserved IDs
            if not any(str(x).encode() in raw for x in ids):continue
            r=json.loads(raw); key=r.get('id',r.get('mathdb_id'))
            if key is None: 
                key=next((x for x in ids if str(x) in str(r.get('url',''))),None)
            try:key=int(key)
            except:continue
            if key not in ids:continue
            (L/'inputs'/f'{key}.raw.jsonl').write_bytes(raw)
            out[str(key)]={'chunk':str(p),'line_1based':i,'raw_sha256':hashlib.sha256(raw).hexdigest(),'record':r}
            matches.append(key)
    if matches:
        h=hashlib.sha256(p.read_bytes()).hexdigest()
        for x in matches:out[str(x)]['chunk_sha256']=h
(L/'outputs/provenance.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():print(k,json.dumps(v['record'],ensure_ascii=False))
for name in ['ledger.json','prior-campaign-context.json']:
    p=B/name; data=json.loads(p.read_text()); (L/'inputs'/name).write_bytes(p.read_bytes())
print('EXTRACTED',len(out))
