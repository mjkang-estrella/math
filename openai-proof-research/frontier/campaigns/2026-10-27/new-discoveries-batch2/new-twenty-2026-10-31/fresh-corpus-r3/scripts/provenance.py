# Build/verify provenance: corpus line+chunk hashes for all 40 records, and sha256 of every
# downloaded primary/registry file (mtime recorded as retrieval UTC). Run: python3 scripts/provenance.py [--write]
import json, hashlib, pathlib, sys, datetime
P=pathlib.Path(__file__).resolve().parents[1]
corpus=P.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
ok=True
for r in json.load(open(P/'literal-records.json')):
    b=(corpus/r['chunk']).read_bytes(); line=b.decode().splitlines()[r['line']-1]
    ok&=hashlib.sha256(b).hexdigest()==r['chunk_sha256'] and hashlib.sha256(line.encode()).hexdigest()==r['line_sha256'] and json.loads(line)['mathdb_id']==r['id']
files=sorted([p for d in ('sources','sources/web','registry') for p in (P/d).glob('*') if p.is_file() and p.suffix in ('.pdf','.body','.html','.json') and p.name!='receipts.json'])
man={str(p.relative_to(P)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,
      'retrieved_utc_mtime':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat()} for p in files}
if '--write' in sys.argv: json.dump(man,open(P/'artifact-receipts.json','w'),indent=1)
else:
    old=json.load(open(P/'artifact-receipts.json'))
    ok&=all(old[k]['sha256']==v['sha256'] for k,v in man.items() if k in old)
print('corpus 40 records + chunk hashes OK' if ok else 'MISMATCH', len(man),'artifact files')
