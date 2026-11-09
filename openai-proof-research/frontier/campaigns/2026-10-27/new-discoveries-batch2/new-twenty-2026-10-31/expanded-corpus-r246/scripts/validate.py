import pathlib,json,hashlib,zipfile,re,subprocess
D=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert set(rs)==set(map(str,reserved)) and len(rs)==20
for i,r in rs.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and hashlib.sha256(raw).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
receipt=json.loads((D/'http-receipt-manifest.json').read_text())
for p,h in receipt.items():assert hashlib.sha256((D/'sources'/p).read_bytes()).hexdigest()==h
replay=json.loads((D/'replay/full-result.json').read_text());assert replay['status']=='PASS' and all(replay[k]==0 for k in ['build','checker','audit']);assert hashlib.sha256((D/'proof-packet-full.zip').read_bytes()).hexdigest()==replay['packet_sha256']
assert 'LOCAL DECLARATION COUNT 19' in (D/'logs/full-audit.log').read_text()
for name in ['SUMMARY.md','CANDIDATE.md']:assert (D/name).stat().st_size>1000
ps=subprocess.run(['ps','-eo','pid,args'],capture_output=True,text=True).stdout
jobs=[line for line in ps.splitlines() if str(D) in line and 'validate.py' not in line and 'bash -c' not in line and 'ps -eo' not in line]
out={'status':'PASS','entries':20,'raw_and_statement_hashes':20,'receipt_hashes':len(receipt),'full_replay':'PASS','declarations_audited':19,'accepted_credit':0,'candidate_on_hold':'339235','possible_lane_jobs':jobs}
(D/'validation.json').write_text(json.dumps(out,indent=2));print(out)
