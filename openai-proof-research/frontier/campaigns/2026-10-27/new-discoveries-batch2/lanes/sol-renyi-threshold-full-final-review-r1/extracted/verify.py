import json,hashlib,sys,subprocess,zipfile,platform,zlib
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=Path(sys.argv[1]).resolve();out.mkdir(exist_ok=False)
m=json.loads((R/'manifest.json').read_text())
assert {p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file()}==set(m)|{'manifest.json'}
for n,h in m.items():assert sha(R/n)==h,n
import reportlab,PIL,charset_normalizer
t=json.loads((R/'toolchain.json').read_text())
assert platform.python_version()==t['python']
assert sha(Path(sys.executable))==t['python_sha256']
assert reportlab.Version==t['reportlab'] and PIL.__version__==t['pillow']
assert charset_normalizer.__version__==t['charset_normalizer']
assert zlib.ZLIB_RUNTIME_VERSION==t['zlib']
for n,h in t['fonts'].items():assert sha(R/'assets'/n)==h,n
def run(args):
 r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (out/(Path(args[1]).stem+'.log')).write_text(r.stdout)
 assert r.returncode==0,r.stdout[-5000:]
run([sys.executable,str(R/'build_paper.py'),str(out/'paper.pdf')])
run([sys.executable,str(R/'pack.py'),str(out/'packet.zip')])
run([sys.executable,str(R/'component/replay.py'),str(R/'component-source.zip'),str(out/'replay')])
r=json.loads((out/'replay/replay-receipt.json').read_text());assert r['declaration_count']==104
result={'status':'EXTRACTED_REBUILD_AND_FULL_REPLAY_PASS','paper_sha256':sha(out/'paper.pdf'),'packet_sha256':sha(out/'packet.zip'),'replay_receipt_sha256':sha(out/'replay/replay-receipt.json'),'modules':len(r['modules']),'declarations':r['declaration_count']}
(out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
