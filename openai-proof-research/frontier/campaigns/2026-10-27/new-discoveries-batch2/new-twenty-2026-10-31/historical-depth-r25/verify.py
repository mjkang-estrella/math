import pathlib,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((O/'reservation.json').read_text());z=json.loads((O/'results.json').read_text());assert len(z)==40 and set(z)==set(map(str,r['ids']))
for p,h in r['prior_report_hashes'].items():assert H(pathlib.Path(p).read_bytes())==h
for i,x in z.items():
 assert x['accepted_credit']==x['unique_coverage_credit']==0 and x['lean_endpoint'] is None
 p=pathlib.Path(x['raw']['path']);b=p.read_bytes();assert H(b)==x['raw']['chunk_sha256'];line=b.splitlines(keepends=True)[x['raw']['one_based_line']-1];assert line==(O/x['raw']['retained']).read_bytes();assert H(line)==x['raw']['line_sha256'];assert H(x['literal_quantifiers'].encode())==x['statement_sha256']
 for s in x['sources']:assert H((O/s['path']).read_bytes())==s['sha256']
for n in ['receipts','more-receipts','last-receipts']:
 for s in json.loads((O/'sources'/(n+'.json')).read_text()):
  if s.get('status')==200:assert H((O/'sources'/s['file']).read_bytes())==s['sha256']
for s in json.loads((O/'registry-screen.json').read_text())['reused_files']:assert H(pathlib.Path(s['path']).read_bytes())==s['sha256']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','results':len(z),'selected_primary_proof_records':sum(x['new_selected_primary_proof_sections_read'] for x in z.values()),'source_problem_texts':sum(x['new_primary_problem_text_read'] for x in z.values()),'credit':0,'lean_endpoint':False,'counts_changed':False};(O/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
manifest={str(p.relative_to(O)):{'sha256':H(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verify.log']};(O/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(receipt,indent=2))
