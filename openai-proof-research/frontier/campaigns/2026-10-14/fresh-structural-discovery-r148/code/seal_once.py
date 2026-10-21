"""Seal the exclusive r148 root exactly once; print detached anchors, write no log after sealing."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.dont_write_bytecode=True
from verify import inventory,digest
ROOT=Path(__file__).resolve().parents[1]
assert ROOT.name=='fresh-structural-discovery-r148'
p=ROOT/'MANIFEST.json'
if p.exists():raise SystemExit('Already sealed: refusing to regenerate manifest')
for n in ['FINAL.md','REPORT.md']:assert (ROOT/n).is_file()
p.write_text(json.dumps(inventory(ROOT),indent=2,sort_keys=True)+'\n')
anchors={}
for n in ['FINAL.md','MANIFEST.json','REPORT.md']:
    h=digest(ROOT/n)
    external=subprocess.check_output(['sha256sum',str(ROOT/n)],text=True).split()[0]
    assert h==external,'Independent detached digest mismatch'
    anchors[n]=h
before={'payload':inventory(ROOT),'envelopes':anchors}
cmd=[sys.executable,'-B',str(ROOT/'code/verify.py'),str(ROOT),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']]
r=subprocess.run(cmd,capture_output=True,text=True,timeout=40)
assert r.returncode==0,(r.stdout,r.stderr)
after={'payload':inventory(ROOT),'envelopes':{n:digest(ROOT/n) for n in anchors}}
assert before==after,'Read-only verification mutated root'
print(json.dumps({'detached_sha256':anchors,'independent_hashlib_and_sha256sum_agree':True,'verifier_result':json.loads(r.stdout),'read_only_before_after_equal':True},indent=2))
