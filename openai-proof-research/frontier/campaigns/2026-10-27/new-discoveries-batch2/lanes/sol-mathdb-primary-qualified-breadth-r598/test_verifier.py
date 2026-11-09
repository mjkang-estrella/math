import pathlib,json,hashlib,tempfile,subprocess,sys
P=pathlib.Path(__file__).resolve().parent;results=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=P) as t:
 T=pathlib.Path(t);b=b'bounded fixture';(T/'item').write_bytes(b)
 m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'item','size':len(b),'sha256':hashlib.sha256(b).hexdigest()}]}
 def run(name,expected):
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-only',str(T)],capture_output=True,text=True);assert (r.returncode==0)==expected
  results.append({'test':name,'exit':r.returncode,'stderr':r.stderr.strip()})
 def put():(T/'manifest.json').write_text(json.dumps(m))
 put();run('positive_fixture',True)
 m['files'][0]['sha256']='0'*64;put();run('hash_rejection',False)
 m['files'][0]['sha256']=hashlib.sha256(b).hexdigest();m['files'][0]['size']+=1;put();run('size_rejection',False)
 m['files'][0]['size']=len(b);put();(T/'extra').write_text('extra');run('extra_file_rejection',False)
(P/'negative-tests.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
