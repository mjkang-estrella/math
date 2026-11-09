from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];R=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];checks={}
checks['exactly_reserved_20']=len(R)==20 and set(map(int,R))==set(ids)
checks['zero_claimed_endpoints']=all(v['credit']==0 and v['lean_endpoint'] is None for v in R.values())
checks['all_raw_hashes_match']=all(hashlib.sha256((L/v['raw_file']).read_bytes()).hexdigest()==v['provenance']['raw_sha256'] and (L/v['raw_file']).read_bytes().endswith(b'\n') for v in R.values())
checks['statement_hashes_match']=all(hashlib.sha256(v['literal_statement'].encode()).hexdigest()==v['statement_sha256'] for v in R.values())
checks['no_bytecode']=not list(L.rglob('__pycache__'))
codes=json.loads((L/'outputs/codes.json').read_text())+json.loads((L/'outputs/codes-extended.json').read_text());checks['88_code_diagnostics_match']=len(codes)==88 and all(v['matches'] for v in codes)
checks['q_source_isomorphism']=json.loads((L/'outputs/q-source-isomorphism.json').read_text())['all_ranks_equal']
checks['eventown_exact_4_cases']=len(json.loads((L/'outputs/eventown-exact.json').read_text()))==4
checks['required_reports_exist']=all((L/x).is_file() for x in ['SUMMARY.md','CANDIDATE.md','results.json'])
bad=[]
for p in (L/'sources').glob('*.receipt.json'):
 d=json.loads(p.read_text());body=Path(str(p)[:-len('.receipt.json')])
 if 'sha256' in d and (not body.is_file() or hashlib.sha256(body.read_bytes()).hexdigest()!=d['sha256']):bad.append(p.name)
checks['http_body_hashes_match']=not bad
out={'checks':checks,'all_pass':all(checks.values()),'bad_receipts':bad};(L/'outputs/validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2));assert out['all_pass']
