from pathlib import Path
import tempfile,json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent;out={};codes={}
guard=D.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=D) as td:
 p=Path(td);(p/'item').write_bytes(b'abc');m={'files':[{'path':'item','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}]};(p/'manifest.json').write_text(json.dumps(m))
 def run():return subprocess.run([sys.executable,'-B',str(guard),sys.executable,'-B',str(D/'verify.py'),'--payload-root',str(p)],capture_output=True,text=True)
 assert run().returncode==0
 for name,b in [('hash_rejected',b'abd'),('size_rejected',b'abcd')]:
  (p/'item').write_bytes(b);r=run();out[name]=r.returncode!=0;codes[name]=dict(exit=r.returncode,stderr=r.stderr)
 (p/'item').write_bytes(b'abc');(p/'extra').write_bytes(b'x');r=run();out['extra_file_rejected']=r.returncode!=0;codes['extra_file_rejected']=dict(exit=r.returncode,stderr=r.stderr)
assert all(out.values());out.update(originals_mutated=False,fixture='synthetic 3-byte payload only; deleted',actual_cli_results=codes);(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
