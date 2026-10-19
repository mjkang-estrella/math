#!/usr/bin/env python3
"""Copies only sealed inputs; writes only to a fresh directory inside --root."""
import argparse,pathlib,hashlib,json,os,stat,shutil,subprocess,sys

def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot(root,exclude=None):
    ans={}
    for p in [root]+sorted(root.rglob('*')):
        if exclude and (p==exclude or exclude in p.parents):continue
        k=str(p.relative_to(root))
        try:s=p.lstat()
        except PermissionError:
            ans[k]={'stat_denied':True};continue
        v={'mode':stat.S_IMODE(s.st_mode),'type':stat.S_IFMT(s.st_mode),'links':s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            try:v.update(size=s.st_size,sha256=sha(p.read_bytes()))
            except PermissionError:v.update(size=s.st_size,read_denied=True)
        elif stat.S_ISLNK(s.st_mode):v['target']=os.readlink(p)
        ans[k]=v
    return ans

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--out',default='copied-controls');ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);a=ap.parse_args();root=a.root.resolve();out=root/a.out
    if out.exists() or root not in out.resolve().parents:raise ValueError('need fresh owned output subtree')
    out.mkdir(parents=True);before=snapshot(root,out);rows=[]
    cases=['baseline','missing-final-argument','wrong-final-hash','wrong-report-hash','proof-change','scope-change','prefreeze-change','payload-missing','extra-file','extra-directory','missing-directory','payload-symlink','payload-hardlink','manifest-change','final-change','outside-report-change','verifier-change','file-mode','directory-mode','read-denied','directory-access-denied','canonical-metadata-change','tree-change','primary-change','audit-write','audit-process']
    for case in cases:
        c=out/case;c.mkdir();shutil.copytree(root/'packet',c/'packet');shutil.copy2(root/'FINAL.json',c/'FINAL.json');shutil.copy2(root/'REPORT.md',c/'REPORT.md');p=c/'packet';fh=a.finalhash;rh=a.reporthash
        target=p/'public/proof.md';v=p/'public/verify.py'
        if case=='wrong-final-hash':fh='0'*64
        elif case=='wrong-report-hash':rh='0'*64
        elif case in ['proof-change','scope-change','prefreeze-change','verifier-change','manifest-change','final-change','outside-report-change','canonical-metadata-change','tree-change','primary-change']:
            names={'proof-change':target,'scope-change':p/'public/FROZEN-SCOPE.md','prefreeze-change':p/'public/prefreeze.md','verifier-change':v,'manifest-change':p/'MANIFEST.json','final-change':c/'FINAL.json','outside-report-change':c/'REPORT.md','canonical-metadata-change':p/'private/upstream-register.json','tree-change':next((p/'private/context').glob('*preprints-tree.json')),'primary-change':p/'private/primary/jiang.pdf'}
            z=names[case];z.write_bytes(z.read_bytes()+b'\n')
        elif case=='payload-missing':target.unlink()
        elif case=='extra-file':(p/'extra').write_text('x')
        elif case=='extra-directory':(p/'extra-dir').mkdir()
        elif case=='missing-directory':shutil.rmtree(p/'private/history')
        elif case=='payload-symlink':target.unlink();target.symlink_to('report.md')
        elif case=='payload-hardlink':target.unlink();os.link(p/'public/report.md',target)
        elif case=='file-mode':target.chmod(0o600)
        elif case=='directory-mode':(p/'public').chmod(0o700)
        elif case=='read-denied':target.chmod(0)
        elif case=='directory-access-denied':(p/'private/history').chmod(0o600)
        argv=[sys.executable,str(v),'--root',str(c),'--reporthash',rh]
        if case!='missing-final-argument':argv+=['--finalhash',fh]
        if case.startswith('audit-'):
            operation="open('forbidden-output','w')" if case=='audit-write' else "__import__('subprocess').run(['true'])"
            argv=[sys.executable,'-c',"import runpy; runpy.run_path("+repr(str(v))+",run_name='control_import'); "+operation]
        sb=snapshot(c);r=subprocess.run(argv,cwd=c,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'});sa=snapshot(c)
        expected=0 if case=='baseline' else (2 if case=='missing-final-argument' else 1)
        ok=r.returncode==expected and sb==sa
        rows.append({'case':case,'returncode':r.returncode,'expected':expected,'unchanged_copy':sb==sa,'expected_result':ok,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        # Restore access on disposable inputs solely for removal.
        for z in c.rglob('*'):
            if z.is_dir():z.chmod(0o755)
            elif z.is_file() and not z.is_symlink():z.chmod(0o644)
        shutil.rmtree(c)
    after=snapshot(root,out);receipt={'status':'COPIED_INTEGRITY_CONTROLS_ONLY','cases':rows,'all_expected':all(x['expected_result'] for x in rows),'whole_preexisting_owned_root_unchanged':before==after,'snapshot_sha256':sha(json.dumps(before,sort_keys=True).encode()),'mathematical_gate':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='cases'},sort_keys=True))
    return 0 if receipt['all_expected'] and before==after else 1
if __name__=='__main__':sys.exit(main())
