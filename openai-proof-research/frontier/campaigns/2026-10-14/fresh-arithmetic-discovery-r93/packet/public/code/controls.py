#!/usr/bin/env python3
"""Copied controls only. Writes confined to OWN/control-work, removed before return.
Original code MIT. Does not modify the source packet or invoke a mathematical test.
"""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    result={}
    for p in sorted([root,*root.rglob('*')]):
        s=p.lstat();r=p.relative_to(root).as_posix()
        result[r]=(stat.S_IMODE(s.st_mode),s.st_nlink, 'D' if p.is_dir() else ('L'+os.readlink(p) if p.is_symlink() else sha(p)))
    return result

def reseal(copy):
    p=copy/'packet';mp=p/'MANIFEST.json';m=json.loads(mp.read_text())
    for r,rec in m['files'].items():
        q=p/r;rec['sha256']=sha(q);rec['bytes']=q.stat().st_size
    mp.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    fp=copy/'FINAL.json';f=json.loads(fp.read_text());f['manifest_sha256']=sha(mp);fp.write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
    return sha(fp)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--final-sha256',required=True);a=ap.parse_args();root=Path(a.root).resolve()
    assert sha(root/'FINAL.json')==a.final_sha256
    work=root/'control-work';assert not work.exists()
    before=snapshot(root);work.mkdir();f=json.loads((root/'FINAL.json').read_text());results=[]
    cases=['baseline','wrong-detached','changed-proof','missing-proof','extra-file','extra-directory','payload-symlink','payload-mode','payload-hardlink','changed-manifest','changed-report','canonical-metadata-new-anchor','source-blob-new-anchor','freeze-receipt-new-anchor']
    try:
      for case in cases:
        c=work/'copy';c.mkdir();shutil.copytree(root/'packet',c/'packet')
        for r in ['FINAL.json',*f['root_files']]:shutil.copy2(root/r,c/r)
        anchor=a.final_sha256;proof=c/'packet/public/proof.md'
        if case=='wrong-detached':anchor='0'*64
        if case=='changed-proof':proof.write_bytes(proof.read_bytes()+b'\nMUTANT\n')
        if case=='missing-proof':proof.unlink()
        if case=='extra-file':(c/'packet/public/extra').write_text('x')
        if case=='extra-directory':(c/'packet/public/extra').mkdir()
        if case=='payload-symlink':proof.unlink();proof.symlink_to('FROZEN.md')
        if case=='payload-mode':proof.chmod(0o600)
        if case=='payload-hardlink':os.link(proof,work/'external-hardlink')
        if case=='changed-manifest':(c/'packet/MANIFEST.json').write_bytes((c/'packet/MANIFEST.json').read_bytes()+b' ')
        if case=='changed-report':(c/'REPORT.md').write_text('mutant')
        if case=='canonical-metadata-new-anchor':
            p=c/'packet/public/canonical.json';x=json.loads(p.read_text());x[0]['canonical']['size']+=1;p.write_text(json.dumps(x));anchor=reseal(c)
        if case=='source-blob-new-anchor':
            p=c/'packet/public/canonical.json';x=json.loads(p.read_text());b=c/'packet'/x[0]['local'];data=b.read_bytes();b.write_bytes(b'!'+data[1:]);x[0]['sha256']=sha(b);p.write_text(json.dumps(x));anchor=reseal(c)
        if case=='freeze-receipt-new-anchor':
            p=c/'packet/public/freeze.json';x=json.loads(p.read_text());x['sha256']='0'*64;p.write_text(json.dumps(x));anchor=reseal(c)
        cb=snapshot(c)
        run=subprocess.run([sys.executable,'-B',str(c/'packet/public/code/verify.py'),'--root',str(c),'--final-sha256',anchor],capture_output=True,text=True)
        unchanged=cb==snapshot(c);expected=(run.returncode==0)==(case=='baseline')
        results.append({'case':case,'expected_outcome':expected,'copied_inputs_unchanged':unchanged,'returncode':run.returncode,'output':run.stdout.strip(),'stderr':run.stderr.strip(),'deliberate_new_anchor':case.endswith('new-anchor')})
        if (work/'external-hardlink').exists():(work/'external-hardlink').unlink()
        shutil.rmtree(c)
    finally:shutil.rmtree(work)
    unchanged=before==snapshot(root)
    out={'cases':results,'all_expected':all(x['expected_outcome'] and x['copied_inputs_unchanged'] for x in results),'whole_actual_author_root_unchanged':unchanged,'source_final_sha256':a.final_sha256,'mathematical_gate':False,'limits':'Exact copied verifier is unmodified. Three cases deliberately reseal copied test anchors to exercise internal provenance checks. Root preservation compares bytes, paths, modes and link counts before and after temporary workspace removal; it excludes no preexisting author files. Receipt is stdout, written separately only after comparison.'}
    print(json.dumps(out,indent=2));return 0 if out['all_expected'] and unchanged else 1
if __name__=='__main__':sys.exit(main())
