import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text())
assert len(r)==20 and set(map(int,r))==set(reservation['ids'])
chunks={}
for i,o in r.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();p=o['provenance'];assert raw.endswith(b'\n')
 assert hashlib.sha256(raw).hexdigest()==p['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==p['statement_utf8_sha256']
 assert json.loads(raw)['mathdb_id']==int(i)
 cp=pathlib.Path(p['chunk'])
 if str(cp) not in chunks:
  b=cp.read_bytes();chunks[str(cp)]=(hashlib.sha256(b).hexdigest(),b.splitlines(keepends=True))
 assert chunks[str(cp)][0]==p['chunk_sha256']
 assert chunks[str(cp)][1][p['line_1based']-1]==raw
 assert not o['proposed_for_acceptance'] and o['lean_packet'] is None
assert len(list((D/'raw').glob('*.jsonl')))==20
assert all(json.loads(p.read_text()).get('truncated') is False for p in [D/'sources/omega-D5-tree.json',D/'sources/omega-Problems-tree.json'])
for name in ['recurrence','recurrence-intended','divine','tiles','tiles-deep','trees','blowups','grids','grids-deep']:
 assert (D/'outputs'/f'{name}.json').exists(),name
 print(name,'output present')
print('PASS: exactly20 reserved IDs; raw bytes, newline, one-based lines, chunk hashes, statement hashes; no acceptance/Lean claim; complete registry scope receipts.')
