import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];R=json.loads((D/'reservation.json').read_text());O=json.loads((D/'results.json').read_text());checks=[]
assert len(O)==40 and set(O)=={str(i) for i in R['ids']}
for i,x in O.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();p=x['provenance'];assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==p['raw_sha256'];raw=json.loads(b);assert raw['statement']==x['statement'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==p['statement_utf8_sha256'];assert x['credit']==0
 source=pathlib.Path(p['chunk']);data=source.read_bytes();assert hashlib.sha256(data).hexdigest()==p['chunk_sha256'];assert data.splitlines(keepends=True)[p['line_1based']-1]==b
 if x['primary_pdf_sha256']:
  a=x['source_url'].split('/')[-1];assert hashlib.sha256((D/'sources'/(a+'.pdf')).read_bytes()).hexdigest()==x['primary_pdf_sha256'];assert x['primary_source_receipt']['sha256']==x['primary_pdf_sha256']
 checks.append(i)
for p in (D/'outputs').glob('*-run.json'):
 r=json.loads(p.read_text());assert r['exit'] in [0,1],(str(p),r['exit'])
# Reports make no formal endpoint claim.
assert not list(D.rglob('*.lean'))
(D/'outputs/validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'IDs_verified':checks,'raw_lines_and_chunk_hashes':'PASS','source_pdf_receipt_hashes':'PASS','no_Lean_endpoint':True,'credit':0},indent=2)+'\n')
print('PASS:40 ID keys, raw newline/line/chunk/statement hashes, primary PDF receipt hashes; zero credit; no Lean endpoint.')
