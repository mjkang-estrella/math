from work import *
import subprocess,traceback
def verify():
 count=0
 for r in json.loads((L/'bindings.json').read_text()):
  assert sha((L/r['copy']).read_bytes())==r['sha256'],r
  if r['kind']!='administrative snapshot only':assert sha(Path(r['original']).read_bytes())==r['sha256'],r
  count+=1
 scientific=json.loads((L/'scientific-freeze.json').read_text())
 for r in scientific:
  assert sha((L/r['original']).read_bytes())==r['sha256'],r
  assert sha((L/r['copy']).read_bytes())==r['sha256'],r
 references=0
 for fn in ['qualified-original-index.json','alias-refresh.json']:
  for r in json.loads((L/fn).read_text())['records']:
   assert sha(Path(r['snapshot_reference']).read_bytes())==r['sha256'],r
   references+=1
 for name in ['projection','closest']:
  r=subprocess.run(['pdftotext','-layout',str(L/'frozen'/(name+'.pdf')),'-'],capture_output=True)
  assert r.returncode==0 and r.stdout==(L/(name+'.txt')).read_bytes(),name
 r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,timeout=40)
 assert r.returncode==0,r.stderr
 assert json.loads(r.stdout)==json.loads((L/'check-results.json').read_text())
 m=json.loads((L/'manifest.json').read_text());excluded=m['explicit_exclusions']
 assert set(excluded)=={'manifest.json','verification-receipt.json'}
 actual={str(p.relative_to(L)):sha(p.read_bytes()) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
 assert actual==m['files'],'manifest coverage/content differs'
 return dict(status='PASS',utc=utc(),assigned_bindings=count,scientific_pairs=len(scientific),
             immutable_reference_bindings=references,checker_replay='exact JSON equality',
             text_extractions='byte equality',manifest_files=len(actual),
             manifest_sha256=sha((L/'manifest.json').read_bytes()),
             exclusions=excluded,administrative_live_bindings=False)
if __name__=='__main__':
 try:r=verify()
 except Exception:
  r=dict(status='FAIL',utc=utc(),traceback=traceback.format_exc());dump('verification-receipt.json',r);raise
 dump('verification-receipt.json',r);print(json.dumps(r))
