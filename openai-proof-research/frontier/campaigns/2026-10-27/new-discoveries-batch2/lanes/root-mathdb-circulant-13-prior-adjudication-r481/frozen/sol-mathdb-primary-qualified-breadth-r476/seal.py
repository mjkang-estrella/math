import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent
files=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','final-receipt.jsonl'}]
(D/'manifest.json').write_text(json.dumps({'excluded_paths':['manifest.json','final-receipt.jsonl'],'files':files},indent=2)+'\n')
