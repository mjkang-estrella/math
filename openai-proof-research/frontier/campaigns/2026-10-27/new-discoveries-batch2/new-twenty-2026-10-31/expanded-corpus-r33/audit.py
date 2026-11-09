"""Read-only integrity audit; run after finalize.py. No formal verification implied."""
import pathlib,json,hashlib
p=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'results.json').read_text());s=json.loads((p/'reservation.json').read_text());d=json.loads((p/'literal-provenance.json').read_text())
assert set(r)==set(map(str,s['ids']))==set(d) and len(r)==40
for i,v in d.items():
 raw=(p/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert h(raw)==v['raw_sha256'];rec=json.loads(raw)
 assert rec['mathdb_id']==int(i);assert h(rec['statement'].encode())==v['statement_sha256'];assert r[i]['literal_statement']==rec['statement'];assert r[i]['accepted_credit']==0
 chunk=pathlib.Path(v['chunk']);assert h(chunk.read_bytes())==v['chunk_sha256'];assert chunk.read_bytes().splitlines(keepends=True)[v['line_1based']-1]==raw
for f in ['source-receipts.json','extra-source-receipts.json']:
 for a in json.loads((p/f).read_text()):
  name=a['name'];matches=list((p/'sources').glob(name+'.*'));matches=[x for x in matches if x.suffix!='.txt'];assert any(h(x.read_bytes())==a['sha256'] for x in matches)
print('PASS: exact40 IDs; exact chunk lines/newlines; raw, statement and retrieved source hashes; zero credit. Not a Lean or mathematical proof audit.')
