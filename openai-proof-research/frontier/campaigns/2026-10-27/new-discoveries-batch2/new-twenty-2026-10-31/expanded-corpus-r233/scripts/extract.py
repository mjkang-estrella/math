import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parents[1]; B=P.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
ids=set(json.loads((P/'reservation.json').read_text())['ids']); out={}
for f in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    data=f.read_bytes()
    for n,line in enumerate(data.splitlines(keepends=True),1):
        row=json.loads(line)
        if row['mathdb_id'] in ids:
            k=str(row['mathdb_id']); (P/'inputs'/f'{k}.jsonl').write_bytes(line)
            out[k]={'chunk':str(f),'line':n,'chunk_sha256':sha(data),'raw_sha256':sha(line),'statement_sha256':sha(row['statement'].encode()),'record':row}
assert len(out)==20
(P/'inputs/provenance.json').write_text(json.dumps(out,indent=2))
for k,v in out.items(): print(k,v['record']['title'],'\n',v['record']['statement'],'\n')
