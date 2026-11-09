import pathlib,json,hashlib,subprocess,shutil,datetime
D=pathlib.Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def sig(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def manifest():
 x={'excluded_exact_paths':EX,'files':[dict(path=str(p.relative_to(D)),**sig(p)) for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in EX]};(D/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
manifest();results=[]
# Only this lane's payload copied, never corpus/history. Each negative changes a separate disposable copy.
for kind in ['hash','size','extra-file']:
 T=D/('.negative-'+kind);T.mkdir()
 try:
  for p in list(D.iterdir()):
   if p.is_file():shutil.copyfile(p,T/p.name)
  target=T/'proposals.json'
  if kind=='hash':target.write_bytes(b'{}\n') # [] newline => {} newline, same size
  elif kind=='size':target.write_bytes(target.read_bytes()+b' ')
  else:(T/'unexpected.txt').write_text('unexpected')
  p=subprocess.run(['python3','-B',str(D/'verify.py'),str(T)],capture_output=True,text=True)
  assert p.returncode!=0,(kind,p.stdout)
  expected={'hash':'hash mismatch','size':'size mismatch','extra-file':'extra/missing payload'}[kind];assert expected in p.stderr,p.stderr
  results.append({'mutation':kind,'exit_code':p.returncode,'stderr':p.stderr.strip(),'originals_mutated':False})
 finally:shutil.rmtree(T)
(D/'negative-tests.json').write_text(json.dumps(results,indent=2)+'\n')
manifest()
p=subprocess.run(['python3','-B',str(D/'verify.py')],capture_output=True,text=True);assert p.returncode==0,p.stderr
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':sig(D/'manifest.json'),'verifier':sig(D/'verify.py'),'exit_code':p.returncode,'result':json.loads(p.stdout),'bounded_negative_rejections':results,'guard':'Invoked inside unchanged fixed helper_guard.py,512MiB AS/groupRSS,CPU210s,wall230s','not_math_or_novelty_pass':True}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
