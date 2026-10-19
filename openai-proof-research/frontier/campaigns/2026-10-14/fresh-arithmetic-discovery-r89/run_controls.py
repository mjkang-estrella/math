#!/usr/bin/env python3
"""Original MIT disposable-copy integrity controls; never a math test."""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def jwrite(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def snapshot(root):
    return {str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file() and not p.is_symlink() and 'control-work' not in p.parts and p.name not in {'control-results.json','HANDOFF.md'}}
def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--tree',type=Path,required=True);a=p.parse_args();r=a.root.resolve();tree=a.tree.resolve()
    before=snapshot(r); work=r/'control-work';work.mkdir(exist_ok=False);results=[]
    def run(name,mutate=None,omit=None,newanchor=False):
        c=work/name;c.mkdir();shutil.copytree(r/'packet',c/'packet')
        for f in ['verify.py','run_controls.py','REPORT.md','FINAL.json']:shutil.copy2(r/f,c/f)
        fh,rh=sha(r/'FINAL.json'),sha(r/'REPORT.md')
        if mutate:mutate(c)
        if newanchor:
            mf=json.loads((c/'packet/MANIFEST.json').read_text())
            for f in mf['files']:
                b=(c/'packet'/f['path']).read_bytes();f.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
            jwrite(c/'packet/MANIFEST.json',mf)
            final=json.loads((c/'FINAL.json').read_text());final['manifest_sha256']=sha(c/'packet/MANIFEST.json');jwrite(c/'FINAL.json',final);fh=sha(c/'FINAL.json')
        cmd=[sys.executable,'-B',str(c/'verify.py'),'--root',str(c),'--tree',str(tree),'--finalhash',fh,'--reporthash',rh]
        if omit:
            idx=cmd.index(omit);del cmd[idx:idx+2]
        proc=subprocess.run(cmd,capture_output=True,text=True,timeout=40)
        expect=0 if name=='baseline' else 1
        ok=(proc.returncode==0) if expect==0 else (proc.returncode!=0)
        results.append({'case':name,'expected':'accept' if expect==0 else 'reject','returncode':proc.returncode,'matched':ok,'stdout':proc.stdout,'stderr':proc.stderr})
        shutil.rmtree(c)
    target='packet/public/other-screens.md'
    run('baseline');run('missing-final',omit='--finalhash');run('missing-report',omit='--reporthash')
    run('changed-final',lambda c:(c/'FINAL.json').write_text((c/'FINAL.json').read_text()+' '))
    run('changed-report',lambda c:(c/'REPORT.md').write_text('changed'))
    run('changed-payload',lambda c:(c/target).write_text('changed'))
    run('missing-payload',lambda c:(c/target).unlink())
    run('extra-payload',lambda c:(c/'packet/extra.txt').write_text('extra'))
    run('extra-directory',lambda c:(c/'packet/extra-directory').mkdir())
    run('symlink-payload',lambda c:((c/target).unlink(),(c/target).symlink_to(c/'packet/public/report.md')))
    run('changed-code',lambda c:(c/'verify.py').write_text((c/'verify.py').read_text()+'\n# changed\n'))
    run('changed-manifest',lambda c:(c/'packet/MANIFEST.json').write_text('{}'))
    def alter(c,which):
        f=c/'packet/private/acquisition.json';v=json.loads(f.read_text())
        if which=='canonical':v[0]['canonical']['mode']='100755'
        else:v[0]['pinned_url']='https://example.invalid/unpinned'
        jwrite(f,v)
    run('new-anchor-bad-canonical',lambda c:alter(c,'canonical'),newanchor=True)
    run('new-anchor-bad-url',lambda c:alter(c,'url'),newanchor=True)
    # Directly exercise the exact own verifier audit-hook code, with all attempted writes confined here.
    for name,code in [('denied-write',"open(str(root/'forbidden.txt'),'w')"),('denied-network',"socket.socket()")]:
        script="import runpy,socket; from pathlib import Path; m=runpy.run_path(%r); root=Path(%r); m['lock_down'](); %s"%(str(r/'verify.py'),str(work),code)
        proc=subprocess.run([sys.executable,'-B','-c',script],capture_output=True,text=True,timeout=20)
        results.append({'case':name,'expected':'reject','returncode':proc.returncode,'matched':proc.returncode!=0 and 'READ_ONLY' in proc.stderr,'stdout':proc.stdout,'stderr':proc.stderr})
    assert not (work/'forbidden.txt').exists()
    work.rmdir();after=snapshot(r)
    receipt={'cases':results,'all_expected':all(x['matched'] for x in results),'original_unchanged':before==after,'before':before,'after':after,'mathematical_gate':False}
    jwrite(r/'control-results.json',receipt)
    print(json.dumps({'cases':len(results),'all_expected':receipt['all_expected'],'original_unchanged':receipt['original_unchanged']}))
    return 0 if receipt['all_expected'] and receipt['original_unchanged'] else 1
if __name__=='__main__':sys.exit(main())
