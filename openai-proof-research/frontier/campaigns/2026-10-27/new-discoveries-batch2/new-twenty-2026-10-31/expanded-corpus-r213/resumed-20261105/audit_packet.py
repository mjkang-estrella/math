import pathlib,json,hashlib,ast
L=pathlib.Path(__file__).resolve().parents[1];O=L/'resumed-20261105';r=json.loads((L/'results.json').read_text());reserved=json.loads((L/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,reserved));assert all(x['accepted_credit']==0 and x['lean']['endpoint'] is None for x in r.values());missing=[]
for row in r.values():
 for p in [row['literal']['raw_file'],row['evidence_note'],*row['attempt_logs']]:
  if not (L/p).is_file():missing.append(p)
assert not missing,missing
for p in O.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['packet-manifest.json','packet-audit.json']:
  files.append({'path':str(p.relative_to(L)),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(O/'packet-manifest.json').write_text(json.dumps(files,indent=2))
a={'results_count':20,'ids_exact':True,'accepted_credit':0,'missing_evidence':missing,'all_python_sources_parse':True,'manifest_files':len(files),'no_lean_endpoint_claimed':True}
(O/'packet-audit.json').write_text(json.dumps(a,indent=2));print(json.dumps(a))
