import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];o=json.loads((L/'results.json').read_text());reserve=json.loads((L/'reservation.json').read_text());assert len(o)==20 and set(map(int,o))==set(reserve['ids'])
for i,v in o.items():
 b=(L/v['raw_path']).read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['raw_sha256'];assert hashlib.sha256(v['literal_statement'].encode()).hexdigest()==v['statement_sha256'];assert json.loads(b)['statement']==v['literal_statement']
 assert not v['formal_endpoint_complete'] and v['discovery_credit']==0
 if i=='372589':
  v['mathematical_attempts_and_coverage']=v['mathematical_attempts_and_coverage'].replace('even orders 10 and 14','even orders 10, 12 and 14').replace('HSASM orders 11 and 15','HSASM orders 11, 13 and 15').replace('Additional odd-order divisibility computation in outputs/asm-odd-13.json if completed.','Odd-order 13 division by B13(z,1) gives an integer polynomial quotient with zero remainder for each first-row position; outputs/asm-odd-13.json.')
(L/'results.json').write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
summary=(L/'SUMMARY.md').read_text().replace('orders 10 and 14; HSASM orders 11 and 15','orders 10, 12 and 14; HSASM orders 11, 13 and 15');(L/'SUMMARY.md').write_text(summary)
files={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ('manifest.json','audit.log')}
(L/'outputs/manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':20,'qualifying_nominations':0,'formal_endpoints':0,'files':files},indent=2)+'\n');print('PASS: exact reservation keys, 20 raw newline/hash/statement checks; no credit or formal endpoint claims;',len(files),'files hashed')
