#!/usr/bin/env python3
"""Run unchanged verifiers on private copies. Never modifies the sealed author inputs."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root,exclude=()):
    rows={}
    for base,ds,fs in os.walk(root,followlinks=False):
        bp=Path(base)
        ds[:]=[n for n in ds if n not in exclude]
        for p in [bp]+[bp/n for n in fs]:
            s=p.lstat();k=p.relative_to(root).as_posix()
            rows[k]=[s.st_mode,s.st_nlink,s.st_size if not p.is_dir() else None,digest(p) if p.is_file() and not p.is_symlink() else (os.readlink(p) if p.is_symlink() else None)]
    return rows
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--tree',type=Path,required=True);ap.add_argument('--final-sha256',required=True);ap.add_argument('--report-sha256',required=True);a=ap.parse_args()
r=a.root.resolve(); scratch=r/'control-work';scratch.mkdir(exist_ok=False)
before=snapshot(r,('control-work',));results=[]
cases=['baseline','missing-final-anchor','wrong-final-anchor','wrong-report-anchor','changed-payload','extra-payload','missing-payload','extra-directory','symlink','hardlink','changed-mode','changed-manifest','changed-FINAL','changed-REPORT']
try:
 for case in cases:
    dest=scratch/case;dest.mkdir();shutil.copytree(r/'packet',dest/'packet')
    for n in ['FINAL.json','REPORT.md']:shutil.copy2(r/n,dest/n)
    target=dest/'packet/public/report.md'
    if case=='changed-payload':target.write_bytes(target.read_bytes()+b'\nmutation\n')
    elif case=='extra-payload':(dest/'packet/unlisted').write_text('x')
    elif case=='missing-payload':target.unlink()
    elif case=='extra-directory':(dest/'packet/unlisted-empty').mkdir()
    elif case=='symlink':target.unlink();target.symlink_to('deck-feasibility.md')
    elif case=='hardlink':os.link(target,dest/'packet/alias')
    elif case=='changed-mode':target.chmod(0o600)
    elif case=='changed-manifest':
        p=dest/'packet/MANIFEST.json';p.write_bytes(p.read_bytes()+b' ')
    elif case=='changed-FINAL':
        p=dest/'FINAL.json';p.write_bytes(p.read_bytes()+b' ')
    elif case=='changed-REPORT':
        p=dest/'REPORT.md';p.write_bytes(p.read_bytes()+b' ')
    cmd=[sys.executable,'-B',str(dest/'packet/code/verify.py'),'--root',str(dest),'--tree',str(a.tree.resolve()),'--report-sha256',('0'*64 if case=='wrong-report-anchor' else a.report_sha256)]
    if case!='missing-final-anchor':cmd+=['--final-sha256',('0'*64 if case=='wrong-final-anchor' else a.final_sha256)]
    snap=snapshot(dest);run=subprocess.run(cmd,text=True,capture_output=True);unchanged=snapshot(dest)==snap
    expected=(run.returncode==0) if case=='baseline' else (run.returncode!=0)
    results.append({'case':case,'exit_code':run.returncode,'expected_result':expected,'copy_inputs_unchanged':unchanged,'stdout':run.stdout.strip(),'stderr':run.stderr.strip()})
    if not(expected and unchanged):raise RuntimeError('control failure '+case)
    shutil.rmtree(dest)
 after=snapshot(r,('control-work',));assert before==after,'author root changed'
finally:
 shutil.rmtree(scratch)
receipt={'final_sha256':a.final_sha256,'report_sha256':a.report_sha256,'verifier_sha256':digest(r/'packet/code/verify.py'),'cases':results,'all_expected':all(x['expected_result'] and x['copy_inputs_unchanged'] for x in results),'author_root_unchanged_during_replay':before==after,'comparison':'all author paths except transient control-work; modes, nlinks, file sizes and SHA256, directory modes/nlinks; receipt written only after comparison','limits':'artifact controls only; no mathematical tests; tampering rejected under original detached anchors, no malicious resealing or exhaustive syscall-denial suite'}
(r/'integrity-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'cases':len(results),'all_expected':receipt['all_expected'],'author_root_unchanged':receipt['author_root_unchanged_during_replay']}))
