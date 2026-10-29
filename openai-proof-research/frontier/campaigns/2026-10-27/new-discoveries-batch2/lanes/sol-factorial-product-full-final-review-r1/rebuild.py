from pathlib import Path
import subprocess,sys,os,hashlib,json
L=Path(__file__).resolve().parent;R=L/'extracted'
env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(L.parent/'sol-factorial-product-manuscript-packet-r1/python-deps')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(R)):sha(p) for p in R.rglob('*') if p.is_file()}
for script in ['certificate.py','build_paper.py']:
 p=subprocess.run([sys.executable,str(R/script)],env=env,capture_output=True,text=True)
 (L/(script+'.log')).write_text(p.stdout+p.stderr);assert p.returncode==0
assert before=={str(p.relative_to(R)):sha(p) for p in R.rglob('*') if p.is_file()}
subprocess.run([sys.executable,str(R/'pack.py'),str(L/'rebuilt.zip')],env=env,check=True)
assert sha(L/'rebuilt.zip')==sha(L.parent/'sol-factorial-product-manuscript-packet-r1/packet.zip')
(L/'rebuild-receipt.json').write_text(json.dumps({'status':'BYTE_IDENTICAL','pdf':sha(R/'paper.pdf'),'zip':sha(L/'rebuilt.zip'),'all_extracted_files_unchanged':True},indent=2)+'\n')
