#!/usr/bin/env python3
"""Optional tamper diagnostics; writes only disposable children of r9. MIT."""
import sys
sys.dont_write_bytecode=True
import hashlib,json,os,shutil,subprocess
from pathlib import Path
R=Path(__file__).resolve().parent
W=R/'.mutation-work'
assert not W.exists()
W.mkdir()
anchor=hashlib.sha256((R/'seal.json').read_bytes()).hexdigest()
rows=[]
try:
    base=W/'base'
    shutil.copytree(R,base,ignore=shutil.ignore_patterns('.mutation-work'))
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    def run(p,a):
        q=subprocess.run([sys.executable,'-B',str(p/'verify.py'),a],cwd=p,env=env,capture_output=True,timeout=90)
        return q
    def snapshot(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file() and not f.is_symlink()}
    before=snapshot(base);q=run(base,anchor)
    assert q.returncode==0,q.stderr
    assert before==snapshot(base)
    rows.append({'case':'unchanged_copy','accepted':True,'read_only':True})
    specs=['bad_external_anchor','altered_payload','extra_file','missing_payload','symlink','bad_git_tree_anchor_resealed']
    for name in specs:
        p=W/name;shutil.copytree(base,p);a=anchor
        if name=='bad_external_anchor':a='0'*64
        elif name=='altered_payload':
            f=p/'candidate.md';f.write_bytes(f.read_bytes()+b'\nTAMPER\n')
        elif name=='extra_file':(p/'unexpected.txt').write_text('tamper\n')
        elif name=='missing_payload':(p/'checks-receipt.json').unlink()
        elif name=='symlink':(p/'unexpected-link').symlink_to('candidate.md')
        elif name=='bad_git_tree_anchor_resealed':
            f=p/'inputs/private/context/sources/preprints-tree.json';t=json.loads(f.read_text())
            wanted='preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/build/main.tex'
            item=next(x for x in t['tree'] if x['path']==wanted);item['sha']='0'*40
            f.write_text(json.dumps(t,indent=2)+'\n')
            mf=p/'inputs-manifest.json';m=json.loads(mf.read_text());e=next(x for x in m['files'] if x['path']==str(f.relative_to(p)));b=f.read_bytes();e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());mf.write_text(json.dumps(m,indent=2)+'\n')
            sf=p/'seal.json';s=json.loads(sf.read_text());b=mf.read_bytes();s['inputs'].update(size=len(b),sha256=hashlib.sha256(b).hexdigest());sf.write_text(json.dumps(s,indent=2)+'\n');a=hashlib.sha256(sf.read_bytes()).hexdigest();(p/'seal.sha256').write_text(a+'  seal.json\n')
        before=snapshot(p);q=run(p,a);assert q.returncode!=0,(name,q.stdout)
        assert before==snapshot(p),name
        error=q.stderr.decode().strip();assert error.startswith('FAIL:'),error
        if name=='bad_git_tree_anchor_resealed':assert 'Git blob mismatch' in error,error
        rows.append({'case':name,'rejected':True,'read_only':True,'reason':error})
finally:
    shutil.rmtree(W)
print(json.dumps({'status':'PASS_DISPOSABLE_TAMPER_DIAGNOSTICS_ONLY','cases':rows,'originals_mutated':False,'mathematical_gate':False},indent=2,sort_keys=True))
