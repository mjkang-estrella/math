import pathlib,json,hashlib,datetime
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');r=json.loads((D/'results.json').read_text());ids=set(map(str,json.loads((D/'reservation.json').read_text())['ids']));assert set(r)==ids and len(r)==20
for mid,x in r.items():
 raw=(D/f'raw/{mid}.jsonl').read_bytes();assert raw.endswith(b'\n');j=json.loads(raw)
 assert j['statement']==x['literal_statement'];assert hashlib.sha256(raw).hexdigest()==x['provenance']['raw_sha256'];assert hashlib.sha256(j['statement'].encode()).hexdigest()==x['provenance']['statement_sha256'];assert hashlib.sha256((D/x['source_pdf']).read_bytes()).hexdigest()==x['source_pdf_sha256'];assert x['credit']==0 and x['lean_endpoint'] is None
for p in ['SUMMARY.md','CANDIDATE.md','outputs/registry-screen.json','outputs/check.json','outputs/snakes-exact-11.json']:assert (D/p).is_file()
receipts={p.stem:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')};bad={k:v for k,v in receipts.items() if v['returncode']!=0};assert set(bad)=={'history.receipt'},bad
http=[json.loads(l) for l in (D/'outputs/http.jsonl').read_text().splitlines()];denied=[x for x in http if x.get('status') in [403,429]];assert not denied
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_count':20,'raw_bindings_checked':20,'source_pdf_bindings_checked':20,'credit':0,'qualified_Lean_endpoints':0,'nonzero_jobs':bad,'http_requests':len(http),'403_429':denied,'separate_tree_checker':'logs/check.log','no_full_solution_claim':True}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest-sha256.json'};(D/'outputs/manifest-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
