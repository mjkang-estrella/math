import pathlib,json,hashlib,datetime,os
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids)) and len(r)==20
for i,x in r.items():
 assert hashlib.sha256((D/f'raw/{i}.jsonl').read_bytes()).hexdigest()==x['provenance']['raw_sha256']
 assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 x=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'))
 if x.get('sha256'):assert b.exists() and hashlib.sha256(b.read_bytes()).hexdigest()==x['sha256']
assert len(json.loads((D/'outputs/registry-screen.json').read_text())['github_searches'])<=8
for p in (D/'logs').glob('*.json'):
 x=json.loads(p.read_text());assert x['sampled_group_peak']<6*1024**3
notes={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_ids':len(r),'raw_and_statement_hashes':'passed','HTTP_body_hashes':'passed','github_query_count':len(json.loads((D/'outputs/registry-screen.json').read_text())['github_searches']),'Lean_endpoint':None,'timed_out_processes':['tableaux-extended: CPU-limited SIGKILL after completed (3,5); (3,6) incomplete, (6,2) not reached. Not restarted.'],'scope':'Integrity audit only. Not a proof or novelty audit.'}
(D/'outputs/validation.json').write_text(json.dumps(notes,indent=2));print(notes)
