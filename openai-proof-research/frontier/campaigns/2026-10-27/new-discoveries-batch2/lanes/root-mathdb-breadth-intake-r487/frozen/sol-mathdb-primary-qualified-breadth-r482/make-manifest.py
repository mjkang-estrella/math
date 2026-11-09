import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent
files=[{'path':str(p.relative_to(O)),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ('manifest.json','final-receipt.jsonl')]
# Exclusions apply to exact lane-relative filenames, not nested manifest names.
files=[{'path':str(p.relative_to(O)),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in ('manifest.json','final-receipt.jsonl')]
(O/'manifest.json').write_text(json.dumps({'files':files,'excluded_actual_filenames':['manifest.json','final-receipt.jsonl']},indent=2));print(json.dumps({'manifest_payloads':len(files)}))
