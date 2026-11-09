import pathlib,json,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def write(n,z):(D/n).write_text(json.dumps(z,indent=2)+'\n')
def manifest():
 files=[]
 for p in sorted(D.rglob('*')):
  if p.is_file() and str(p.relative_to(D)) not in excluded:
   b=p.read_bytes();files.append(dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 write('manifest.json',dict(excluded_exact_paths=excluded,files=files))
def run(*args):
 r=subprocess.run(['python3','-B',str(D/'verify.py'),*args],capture_output=True,text=True);return dict(exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr)
write('negative-tests.json',{})
write('final-verification-receipt.json',{})
manifest();initial=run();assert initial['exit_code']==0,initial
neg={}
for name in ['hash','size']:
 neg[name]=run('--negative-'+name);assert neg[name]['exit_code']!=0
p=D/'deliberate-extra-file';p.write_bytes(b'bounded negative fixture\n')
try:neg['extra_file']=run();assert neg['extra_file']['exit_code']!=0
finally:p.unlink()
write('negative-tests.json',dict(tests=neg,method='Hash and size expected-manifest entries changed in memory; extra-file test creates/removes one lane-local fixture. No originals or scientific payload bytes mutated.',initial_positive=initial))
manifest();final=run();assert final['exit_code']==0,final
b=(D/'manifest.json').read_bytes();write('final-verification-receipt.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),verification=final,negative_tests={k:v['exit_code'] for k,v in neg.items()},guard='Fixed helper_guard;512MiB AS/groupRSS,CPU210s,wall230s; all scripts run under guard',scientific_status='HOLD; integrity does not imply proof or novelty'))
print(json.dumps(load if False else json.loads((D/'final-verification-receipt.json').read_text()),indent=2))
