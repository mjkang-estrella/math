from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]; B=L.parent
ids=json.loads((B/'root-mathdb-gram-intake-r359/reserved-ids.json').read_text())['ids']; want=set(ids)
bind={r['path']:r for r in json.loads((L/'input-bindings.json').read_text())}
C=B/'pi-mathdb-full-corpus-inventory-r301/corpus'; out={}
for f in sorted(C.glob('*.jsonl')):
    b=f.read_bytes(); assert hashlib.sha256(b).hexdigest()==bind[str(f)]['sha256']
    for i,line in enumerate(b.decode().splitlines(),1):
        d=json.loads(line)
        if d['mathdb_id'] in want:
            assert d['mathdb_id'] not in out
            s=d['statement']; d['corpus_path']=str(f); d['corpus_line']=i
            d['literal_statement_sha256']=hashlib.sha256(s.encode()).hexdigest()
            out[d['mathdb_id']]=d
assert set(out)==want
(L/'records.json').write_text(json.dumps([out[i] for i in ids],indent=1,ensure_ascii=False)+'\n')
print('extracted',len(out))
