import json,pathlib,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parents[1];e=json.loads((D/'extracted.json').read_text());r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text())
assert len(r)==20 and set(map(int,r))==set(reservation['ids'])
for i,x in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256'];raw=json.loads(b);assert raw['statement']==x['statement'];assert hashlib.sha256(raw['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256'];assert hashlib.sha256((D/f'sources/{i}.pdf').read_bytes()).hexdigest()==x['source_pdf_sha256']
 for f in x['artifacts']+x['registry_receipts']+[x['source_receipt']]:assert (D/f).is_file(),f
assert (D/'SUMMARY.md').exists()
ps=subprocess.run(['ps','-eo','pid,ppid,args'],capture_output=True,text=True,check=True).stdout
# Match actual process argv containing this absolute lane; ignore this validator and its wrapper.
active=[s for s in ps.splitlines() if str(D) in s and 'validate.py' not in s and 'exec_command' not in s and 'bash -lc' not in s]
receipts=[]
for p in (D/'logs').glob('*.receipt.json'):
 x=json.loads(p.read_text());receipts.append((p.name,x))
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(r),'all_raw_source_hashes_verified':True,'formal_endpoints':0,'credit':0,'launched_process_receipts':len(receipts),'peak_sampled_rss':max(x['sampled_process_rss_peak_bytes'] for _,x in receipts),'cap_terminations':[(n,x['cap_reason']) for n,x in receipts if x['cap_reason']],'active_lane_processes_excluding_validator':active}
(D/'outputs/validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));assert not active
