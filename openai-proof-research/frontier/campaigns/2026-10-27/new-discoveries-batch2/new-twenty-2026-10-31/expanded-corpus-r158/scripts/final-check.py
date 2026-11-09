import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids']
assert len(r)==20 and set(r)==set(map(str,ids))
for k,v in r.items():
 b=(L/v['raw_file']).read_bytes()
 assert b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256']
 assert hashlib.sha256(v['literal_statement'].encode()).hexdigest()==v['provenance']['statement_sha256']
for f in ['Definitions','Witness','Audit']:
 a=(L/'lean'/f'{f}.lean').read_bytes()
 assert a==(L/'extracted'/f'{f}.lean').read_bytes()==(L/'extracted-replay'/f'{f}.lean').read_bytes()
 assert (L/'extracted-replay'/f'{f}.olean').exists()
 assert not (L/'extracted-replay/logs'/f'{f}.checker.log').read_text().strip()
 s=(L/'extracted-replay/logs'/f'{f}.strict.log').read_text()
 assert 'error:' not in s and 'sorryAx' not in s
assert 'META local=23 flagged=[]' in (L/'extracted-replay/logs/Audit.strict.log').read_text()
print('PASS: 20 exact IDs, raw bytes and statement hashes; extracted source identity; 3 strict builds/checkers; 23 declaration audit.')
print('Candidate archive sha256',hashlib.sha256((L/'lean-packet.tar.gz').read_bytes()).hexdigest())
