import pathlib,json,ast,hashlib,datetime,os
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'logs/cubic-fixed.log';rows=[]
for line in p.read_text().splitlines():
 try:o=ast.literal_eval(line)
 except (ValueError,SyntaxError):continue
 if isinstance(o,dict) and 'n'in o:rows.append(o)
cap=json.loads((D/'logs/cubic-fixed.json').read_text());(D/'outputs/cubic-partial.json').write_text(json.dumps({'completed_batches':rows,'process_result':cap,'limitation':'Unfinished order-32 batch is not covered. Per-instance limited cases have no verdict. No restart after process cap.'},indent=2))
r=json.loads((D/'results.json').read_text())
for i,v in r.items():
 v['source_file_hashes']={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((D/'sources').glob(i+'*.body'))}
 if i=='361462':v['mathematical_attempts']+=' Completed batch counts are archived in outputs/cubic-partial.json. The final order-32 batch did not finish before the process wall cap; no coverage is claimed for it and the job was not restarted.'
(D/'results.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
assert set(r)==set(map(str,json.loads((D/'reservation.json').read_text())['ids'])) and len(r)==20
assert all(v['discovery_credit']==0 for v in r.values())
audit={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_ids':sorted(r),'count':len(r),'new_lean_endpoints':0,'acceptance_claim':False,'resource_jobs':{p.stem:json.loads(p.read_text()) for p in sorted((D/'logs').glob('*.json'))},'scope':'Only this lane was written; no git, browser, accounts, external messages or child agents used','limitations':'Focused primary-body review and bounded search only; all-version PDFs archived but no every-page comparison or complete version-of-record/citing-work clearance. Brief request for several hours of investigation was not achieved.'}
(D/'outputs/final-audit.json').write_text(json.dumps(audit,indent=2))
print('Validated exactly 20 reserved entries; zero credit; all capped numerical jobs finished.')
