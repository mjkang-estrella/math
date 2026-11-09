import json,pathlib,hashlib,re
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parent.parent
res=json.loads((L/'reservation.json').read_text()); ids=set(res['ids'])
cor=B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
out={}
for f in sorted(cor.glob('mathdb-normalized-chunk-*.jsonl')):
    found=[]
    with f.open('rb') as s:
        for i,line in enumerate(s,1):
            if not any(str(k).encode() in line for k in ids):continue
            d=json.loads(line)
            k=d.get('id',d.get('mathdb_id'))
            if k is not None:k=int(k)
            if k not in ids:continue
            (L/'sources'/f'{k}.raw.jsonl').write_bytes(line)
            out[str(k)]={'chunk':str(f),'line':i,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':d}
            found.append(k)
    if found:
        h=hashlib.sha256()
        with f.open('rb') as s:
            for buf in iter(lambda:s.read(1048576),b''):h.update(buf)
        for k in found:out[str(k)]['chunk_sha256']=h.hexdigest()
(L/'outputs/intake.json').write_text(json.dumps(out,indent=2))
print('Found',len(out))
for k,d in out.items():print(k,json.dumps(d['record'],ensure_ascii=False))
