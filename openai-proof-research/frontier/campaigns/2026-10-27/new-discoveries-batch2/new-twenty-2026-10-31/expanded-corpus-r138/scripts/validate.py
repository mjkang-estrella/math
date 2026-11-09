import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text());assert len(r)==20 and set(r)==set(map(str,reservation['ids']))
chunks={}
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');raw=json.loads(b);p=o['provenance'];assert sha(b)==p['raw_sha256'];assert raw['statement']==o['statement'];assert sha(o['statement'].encode())==p['statement_utf8_sha256'];assert o['discovery_credit']==0 and o['lean']['kernel_checked']==False
 cp=pathlib.Path(p['chunk'])
 if cp not in chunks:chunks[cp]=cp.read_bytes()
 assert sha(chunks[cp])==p['chunk_sha256'];assert chunks[cp].splitlines(keepends=True)[p['line_1based']-1]==b
for rec in json.loads((D/'sources/receipts.json').read_text()):
 p=D/f"sources/{rec['id']}.pdf";b=p.read_bytes();assert b.startswith(b'%PDF');assert sha(b)==rec['sha256']
for rec in json.loads((D/'sources/more-receipts.json').read_text()):
 if 'file' in rec:assert sha((D/'sources'/rec['file']).read_bytes())==rec['sha256']
assert 's UNSATISFIABLE' in (D/'logs/forest9-sat.log').read_text()
for name in ['triangle','paw','cycle','diamond','clique']:assert 's UNSATISFIABLE' in (D/f'logs/forest10-{name}-sat.log').read_text()
for name in ['digraph-ramsey','digraph-ramsey2']:
 a=json.loads((D/f'outputs/{name}.json').read_text());assert len(a)==80 and all(x['status']==0 for x in a)
 if name.endswith('2'):assert all(x['min_directed_cut']==2 for x in a)
assert not list(D.rglob('*.lean'))
validation={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'results_count':20,'reserved_ID_match':True,'raw_newlines_lines_and_chunk_hashes':'PASS','source_receipt_hashes':'PASS','new_credit':0,'Lean_endpoint':None,'SAT_statuses':'order9 UNSAT; all five order10 branches UNSAT; solver diagnostics only','remaining_regime_digraph_samples':160,'exact_lambda2_samples':80,'diagnostics_not_proofs':True}
(D/'outputs/validation.json').write_text(json.dumps(validation,indent=2)+'\n')
inv={}
for sub in ['raw','sources','scripts','logs','outputs']:
 for p in sorted((D/sub).rglob('*')):
  if not p.is_file() or p.name.startswith('validate.'):continue
  h=hashlib.sha256()
  with p.open('rb') as f:
   while b:=f.read(1024*1024):h.update(b)
  inv[str(p.relative_to(D))]={'bytes':p.stat().st_size,'sha256':h.hexdigest()}
for name in ['SUMMARY.md','RESEARCH.md','SEARCH.md','results.json','reservation.json','TASK.txt']:
 p=D/name;inv[name]={'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
(D/'evidence-manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excluded_ephemeral_validation_files':'logs/validate.* and scripts/validate.py; manifest does not hash itself','files':inv},indent=2)+'\n')
print(json.dumps(validation,indent=2))
