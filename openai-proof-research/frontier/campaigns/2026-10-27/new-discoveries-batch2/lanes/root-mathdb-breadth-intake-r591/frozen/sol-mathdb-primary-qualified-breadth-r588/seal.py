import json,pathlib,hashlib,datetime,subprocess,copy
import verify
O=pathlib.Path(__file__).resolve().parent
def save(n,x):(O/n).write_text(json.dumps(x,indent=2)+'\n')
def seal():
 rows=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
   b=p.read_bytes();rows.append(dict(path=str(p.relative_to(O)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 save('manifest.json',dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=rows))
seal();tests=[]
for key,value in [('sha256','0'*64),('size',-1)]:
 m=copy.deepcopy(verify.load(O/'manifest.json'));m['files'][0][key]=value
 try:verify.payload(O,m);raise RuntimeError('negative incorrectly accepted')
 except AssertionError as e:tests.append(dict(test=key+' mismatch',result='REJECT',message=str(e)))
p=O/'negative-extra-file.txt'
try:
 p.write_text('intentional bounded exact-payload negative\n')
 result=subprocess.run([__import__('sys').executable,'-B',str(O/'verify.py')],capture_output=True,text=True)
 assert result.returncode!=0 and 'extra/missing' in result.stderr
 tests.append(dict(test='extra file actual CLI',exit_code=result.returncode,result='REJECT',message=result.stderr.strip()))
finally:p.unlink()
save('negative-tests.json',dict(tests=tests,originals_mutated=False,hash_size_mutation='in-memory manifest expectation only'))
seal();result=subprocess.run([__import__('sys').executable,'-B',str(O/'verify.py')],capture_output=True,text=True);assert result.returncode==0,result.stderr
b=(O/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),verifier_exit=result.returncode,result=json.loads(result.stdout),negative_tests=tests,limits='fixed guard unchanged; enclosing process group includes all verifier runs')
save('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
