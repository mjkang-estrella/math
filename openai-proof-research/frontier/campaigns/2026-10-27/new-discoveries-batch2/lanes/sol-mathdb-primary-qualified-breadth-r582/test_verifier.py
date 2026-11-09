from pathlib import Path
import tempfile,shutil,subprocess,json
D=Path(__file__).resolve().parent;out=[]
with tempfile.TemporaryDirectory(prefix='.negative-',dir=D) as td:
 T=Path(td)
 for p in D.iterdir():
  if p.is_file():shutil.copyfile(p,T/p.name)
 def run(case):
  r=subprocess.run(['python3','-B',str(D/'verify.py'),str(T)],capture_output=True,text=True);out.append({'case':case,'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()});return r.returncode
 assert run('unchanged_copy')==0
 p=T/'SUMMARY.md';b=p.read_bytes();p.write_bytes(bytes([b[0]^1])+b[1:]);assert run('same_size_hash_mutation')!=0;p.write_bytes(b)
 p.write_bytes(b+b'X');assert run('size_mutation')!=0;p.write_bytes(b)
 (T/'unexpected.txt').write_text('x');assert run('extra_file')!=0
(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
