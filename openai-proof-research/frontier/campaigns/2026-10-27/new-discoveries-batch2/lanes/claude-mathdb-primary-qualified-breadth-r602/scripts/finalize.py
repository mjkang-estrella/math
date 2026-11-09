# Run negative tests and verify.py under the fixed helper guard; write final-receipt.json (the only file written).
import datetime,hashlib,json,os,subprocess,sys
B=os.path.realpath(sys.argv[1]); ME=os.path.join(B,'lanes','claude-mathdb-primary-qualified-breadth-r602')
G=os.path.join(B,'lanes','sol-edge-irregulator-manuscript-packet-r1','packet','helper_guard.py')
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
def g(args):
    p=subprocess.run([sys.executable,'-B',G,sys.executable,'-B']+args,capture_output=True,text=True,env=env,cwd=B)
    return p.returncode,p.stdout,p.stderr.strip().splitlines()[-1] if p.stderr.strip() else ''
nc,no,ne=g([os.path.join(ME,'scripts','negative_tests.py'),B])
vc,vo,ve=g([os.path.join(ME,'verify.py'),B])
mb=open(os.path.join(ME,'manifest.json'),'rb').read()
rc={'lane':'claude-mathdb-primary-qualified-breadth-r602','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'manifest_sha256':hashlib.sha256(mb).hexdigest(),'manifest_size':len(mb),
 'negative_tests':{'exit':nc,'result':json.loads(no) if no.strip().startswith('{') else no,'guard':ne},
 'verify':{'exit':vc,'result':json.loads(vo) if vo.strip().startswith('{') else vo,'guard':ve},
 'integrity':'PASS' if (nc==0 and vc==0) else 'FAIL','scientific_acceptance':False,'new_literal_record_reviews':50,'proposals':2,'credit':0,
 'note':'Integrity PASS is not a math, novelty or acceptance PASS.'}
json.dump(rc,open(os.path.join(ME,'final-receipt.json'),'w'),indent=1,sort_keys=True)
print(json.dumps({'integrity':rc['integrity'],'neg':nc,'verify':vc,'manifest_sha256':rc['manifest_sha256'],'manifest_size':rc['manifest_size']}))
