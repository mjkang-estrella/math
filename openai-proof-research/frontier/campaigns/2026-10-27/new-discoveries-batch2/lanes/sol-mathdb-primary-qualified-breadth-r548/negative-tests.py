import pathlib,json,shutil,tempfile,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
out=[]
for kind in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as tmp:
  T=pathlib.Path(tmp)
  for p in P.iterdir():
   if p.is_file():shutil.copyfile(p,T/p.name)
  if kind=='extra-file':(T/'UNLISTED').write_text('negative test only')
  else:
   m=json.loads((T/'manifest.json').read_text());e=next(e for e in m['files'] if e['path']=='proposals.json')
   if kind=='hash':e['sha256']='0'*64
   else:e['size']+=1
   (T/'manifest.json').write_text(json.dumps(m))
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),str(T)],capture_output=True,text=True)
  out.append({'kind':kind,'exit_code':r.returncode,'stderr':r.stderr.strip(),'rejected':r.returncode!=0});assert r.returncode!=0
(P/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
