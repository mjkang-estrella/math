import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
files={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps({'created_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'excludes':['final-manifest.json','final-verification-receipt.json']},indent=2))
print(json.dumps({'files':len(files),'manifest_sha256':hashlib.sha256((L/'final-manifest.json').read_bytes()).hexdigest()}))
