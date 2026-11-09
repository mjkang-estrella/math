import pathlib,json,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
for i,o in r.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];a=json.loads(raw);assert a['statement']==o['statement'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['credit_proposed']==0 and o['lean_endpoint'] is None
 rec=json.loads((D/o['source_receipt']).read_text());assert rec['status']==200 and rec['sha256']==o['primary_source_sha256'];assert sha(pathlib.Path(rec['path']).read_bytes())==rec['sha256']
 if o['finite_search']:assert (D/o['finite_search']).exists()
for k in ['D5','Problems']:assert json.loads((D/f'sources/omega-{k}.json').read_text())['truncated'] is False
# Identify only this lane's actual Python research jobs, not unrelated campaign processes.
p=subprocess.run(['ps','-eo','pid,args'],capture_output=True,text=True)
active=[l for l in p.stdout.splitlines() if str(D.resolve()/'scripts') in l and any('/'+x+'.py' in l for x in ['finite','poly','skew','words','complex','atlas','fetch','registry']) and 'python -' not in l and 'bash -' not in l]
assert not active,active
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'id_count':20,'raw_and_statement_hash_checks':True,'primary_body_receipt_checks':True,'complete_omega_scope_flags':True,'lean_endpoints':0,'active_lane_research_processes':active,'status':'artifact consistency PASS; research completion and novelty NOT certified'}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
files={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.name!='MANIFEST.sha256.json'}
(D/'MANIFEST.sha256.json').write_text(json.dumps(files,indent=2)+'\n')
