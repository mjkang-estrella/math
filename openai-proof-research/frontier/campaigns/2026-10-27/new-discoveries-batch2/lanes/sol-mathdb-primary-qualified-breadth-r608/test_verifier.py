import pathlib,json,tempfile,shutil,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
m=json.loads((P/'manifest.json').read_text());out=[]
with tempfile.TemporaryDirectory(prefix='.negative-',dir=P) as t:
 T=pathlib.Path(t)
 for e in m['files']:
  p=T/e['path'];p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(P/e['path'],p)
 shutil.copyfile(P/'manifest.json',T/'manifest.json')
 def run():return subprocess.run([sys.executable,'-B',str(P/'verify.py'),str(T)],capture_output=True,text=True)
 z=run();assert z.returncode==0,z.stderr
 f=T/'proposals.json';original=f.read_bytes()
 for kind,b,marker in [('hash',b'{}\n','hash mismatch'),('size',original+b' ','size mismatch')]:
  f.write_bytes(b);z=run();assert z.returncode!=0 and marker in z.stderr,z.stderr;out.append({'negative':kind,'exit':z.returncode,'specific_rejection':marker});f.write_bytes(original)
 (T/'unexpected.txt').write_text('negative fixture only');z=run();assert z.returncode!=0 and 'extra/missing payload' in z.stderr;out.append({'negative':'extra file','exit':z.returncode,'specific_rejection':'extra/missing payload'})
(P/'negative-tests.json').write_text(json.dumps({'pristine_clone_pass':True,'tests':out,'originals_mutated':False},indent=2)+'\n');print(json.dumps(out))
