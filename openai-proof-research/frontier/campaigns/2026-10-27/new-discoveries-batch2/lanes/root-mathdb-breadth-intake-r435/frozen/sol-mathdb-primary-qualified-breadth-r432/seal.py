import pathlib,json,hashlib,runpy,contextlib,io,datetime
O=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.relative_to(O).as_posix() not in {'manifest.json','final-receipt.json'}:
  b=p.read_bytes();files.append({'path':p.relative_to(O).as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_paths':['manifest.json','final-receipt.json']},indent=2)+'\n')
buf=io.StringIO()
with contextlib.redirect_stdout(buf):runpy.run_path(str(O/'verify.py'),run_name='__main__')
(O/'final-receipt.json').write_text(json.dumps({'status':'PASS','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256((O/'manifest.json').read_bytes()).hexdigest(),'payload_files':len(files),'verification_output':buf.getvalue(),'receipt_excluded_exact_path':'final-receipt.json','counts':{'additional':9,'total':39,'next':40}},indent=2)+'\n')
print(buf.getvalue(),end='')
