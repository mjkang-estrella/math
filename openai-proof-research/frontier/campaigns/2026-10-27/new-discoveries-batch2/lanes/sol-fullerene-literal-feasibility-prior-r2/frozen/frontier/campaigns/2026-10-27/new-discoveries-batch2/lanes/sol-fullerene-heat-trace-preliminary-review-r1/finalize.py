from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=[]
for file in ['freeze.json','extra-freeze.json']:
 for r in json.loads((L/file).read_text()):
  assert h(Path(r['original']))==h(L/r['copy'])==r['sha256'];bindings.append(r)
for r in json.loads((L/'retrieval.json').read_text()):
 if 'sha256' in r:assert h(L/r['copy'])==r['sha256'];bindings.append(r)
r=json.loads((L/'publisher-access.json').read_text());assert h(L/r['copy'])==r['sha256'];bindings.append(r)
(L/'source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
pro={'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'solo independent preliminary reviewer','verdicts':{'SOURCE':'PASS literal arXiv; published-target search bounded','MATH':'PASS','SUBSTANTIVE':'plausible; eligibility HOLD','NOVELTY':'HOLD bounded coverage','FORMAL-FEASIBILITY':'conditional; substantial literal-source interfaces unverified'},'counts_snapshot':{'additional':9,'total':39,'next':40},'credit_decision':'root only; none made','guard':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'limits':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'env':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'checker_code_imported':False,'external_mutations':False,'bindings':'source-bindings.json','mathematical_evidence':'independent-evidence.json'}
(L/'provenance.json').write_text(json.dumps(pro,indent=2)+'\n')
(L/'failures.json').write_text(json.dumps({'reviewer':[{'file':'check-extended.guard.json','failure':'AssertionError: initially assumed reverse rotation convention','resolution':'oriented triangle convention gives forward successor; corrected checker passes','scientific_effect':'none'}],'worker_failures_preserved':'frozen/failures.jsonl','access_denials_retried':False,'coverage_gaps':['no published 2024 target body identified','no original Godsil-McKay body inspected','no exhaustive specialist/current registry proof-file clearance','no Lean feasibility implementation']},indent=2)+'\n')
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print('manifest files',len(manifest))
