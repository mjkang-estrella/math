import pathlib,json,hashlib,datetime,subprocess,importlib.util,tempfile
P=pathlib.Path(__file__).resolve().parent
def h(d):return hashlib.sha256(d).hexdigest()
def write(n,z):(P/n).write_text(json.dumps(z,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('independent_verifier',P/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results={}
# Synthetic bounded fixtures live only in assigned lane and disappear before manifest.
with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as tmp:
 t=pathlib.Path(tmp);q=t/'fixture';q.write_bytes(b'abcd');good={'size':4,'sha256':h(b'abcd')}
 v.check(q,good)
 for name,e in [('wrong_hash',dict(good,sha256='0'*64)),('wrong_size',dict(good,size=5))]:
  try:v.check(q,e)
  except AssertionError:results[name]='rejected'
  else:raise AssertionError('negative accepted '+name)
 m={'files':[dict(good,path='fixture')],'excluded_exact_paths':['manifest.json','final-verification-receipt.json']};v.exact(t,m)
 (t/'extra').write_bytes(b'x')
 try:v.exact(t,m)
 except AssertionError:results['extra_file']='rejected'
 else:raise AssertionError('extra accepted')
write('negative-tests.json',dict(results=results,fixtures='Synthetic only; originals not mutated; exact same check/exact routines as verifier.',guard='512MiB AS/groupRSS, CPU210s, wall230s unchanged'))
files=[]
for q in sorted(P.rglob('*')):
 if q.is_file() and q.name not in ['manifest.json','final-verification-receipt.json']:
  d=q.read_bytes();files.append(dict(path=str(q.relative_to(P)),size=len(d),sha256=h(d)))
write('manifest.json',dict(files=files,excluded_exact_paths=['manifest.json','final-verification-receipt.json']))
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);print(r.stdout,r.stderr);assert r.returncode==0
mb=(P/'manifest.json').read_bytes();write('final-verification-receipt.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),integrity='PASS',verifier_returncode=r.returncode,verifier_result=json.loads(r.stdout),manifest_sha256=h(mb),manifest_size=len(mb),payload_files=len(files),negative_rejections=results,scientific_acceptance=False,novelty_clearance=False,guard_limits='512MiB AS/groupRSS;CPU210s;wall230s',coverage_delta=50,proposals=0))
print('manifest',h(mb),len(mb),'files',len(files))
