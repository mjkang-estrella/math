#!/usr/bin/env python3
# MIT. Re-anchored counterfeit controls for the author's verify.py.
# Run only on a disposable, already authenticated copy of the author packet:
#   author-reason-controls.py COPY_ROOT EXTERNAL_MANIFEST_SHA256
# Every mutation is made in a sibling temporary directory and removed afterwards.
# Each counterfeit rewrites manifest.json so that the inventory is self-consistent and
# passes the anchor check under its own new anchor; the content check must still reject it.
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
base=Path(sys.argv[1]).absolute();anchor=sys.argv[2]
work=Path(tempfile.mkdtemp(prefix='author-reason-',dir=base.parent))
results=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def clone(name):
    d=work/name;shutil.copytree(base,d,symlinks=True)
    return d
def reanchor(d):
    m=json.loads((d/'manifest.json').read_text())
    files={};dirs=[]
    for p in sorted(d.rglob('*')):
        rel=p.relative_to(d).as_posix();st=os.lstat(p)
        if stat.S_ISDIR(st.st_mode):dirs.append(rel)
        elif rel!='manifest.json':files[rel]={'bytes':st.st_size,'sha256':sha(p.read_bytes())}
    m['directories']=sorted(dirs);m['files']=files
    raw=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode()
    (d/'manifest.json').write_bytes(raw)
    return sha(raw)
def run(d,a):
    r=subprocess.run([sys.executable,'-B',str(d/'verify.py'),a],capture_output=True,text=True,cwd=str(work))
    return r.returncode,(r.stdout+r.stderr).strip()
def expect(name,d,a,text):
    code,out=run(d,a)
    ok=code!=0 and ('FAIL: '+text) in out
    results.append({'case':name,'returncode':code,'output':out,'reason_ok':ok})
    if not ok:raise SystemExit('WRONG OUTCOME '+name+': '+out)
def append(d,rel,data=b'\n'):
    p=d/rel;p.write_bytes(p.read_bytes()+data)

try:
    d=clone('positive');code,out=run(d,anchor)
    if code!=0 or 'PASS_EXACT_INVENTORY' not in out:raise SystemExit('positive failed: '+out)
    results.append({'case':'positive','returncode':code,'output':out,'reason_ok':True})
    # The writer must reproduce the author's manifest byte for byte, so counterfeits differ only by the mutation.
    d=clone('reanchored-unchanged');a=reanchor(d)
    if a!=anchor:raise SystemExit('reanchor writer not byte-faithful')
    results.append({'case':'reanchored-unchanged (writer reproduces the author manifest bytes)','anchor':a,'reason_ok':True})
    src='private/source286/preprints/The-arithmetic-category-and-stable-recovery-of-lattice-factors-September-23-2026/build/sections/03-calculus.tex'
    d=clone('reanchored-source-blob');append(d,src,b'%m\n');expect('reanchored-source-blob',d,reanchor(d),'source identity mismatch')
    d=clone('reanchored-primary-body');append(d,'private/primary/Vaes2008.pdf');expect('reanchored-primary-body',d,reanchor(d),'primary identity mismatch')
    d=clone('reanchored-primary-text');append(d,'private/primary/EGNO.txt');expect('reanchored-primary-text',d,reanchor(d),'primary text identity mismatch')
    d=clone('reanchored-context-copy');append(d,'private/context/AGENTS.md');expect('reanchored-context-copy',d,reanchor(d),'context identity mismatch')
    d=clone('reanchored-scope');p=d/'scope286f.md';p.write_bytes(p.read_bytes().replace(b'group-theoretical',b'weakly group-theoretical',1))
    expect('reanchored-scope',d,reanchor(d),'frozen scope mismatch')
    d=clone('reanchored-family-inventory');p=d/'source-family-inventory.json';inv=json.loads(p.read_text());inv['entries']=inv['entries'][:-1]
    p.write_text(json.dumps(inv));expect('reanchored-family-inventory',d,reanchor(d),'source family completeness mismatch')
finally:
    shutil.rmtree(work)
print(json.dumps({'integrity_only':True,'all_reasons_ok':True,'results':results},indent=1))
