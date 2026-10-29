import pathlib,json
L=pathlib.Path(__file__).resolve().parent
for lane in ['sol-mmpp-survival-preliminary-review-r1','sol-mmpp-historical-prior-review-r2']:
 d=json.loads((L/'context'/lane/'provenance.json').read_text());print(lane,json.dumps({k:v for k,v in d.items() if not isinstance(v,dict) or k not in ['hashes','files','artifacts','evidence_hashes']},indent=2)[:18000])
print((L/'context/sol-mmpp-survival-preliminary-review-r1/source-prior-evidence.json').read_text()[:15000])
