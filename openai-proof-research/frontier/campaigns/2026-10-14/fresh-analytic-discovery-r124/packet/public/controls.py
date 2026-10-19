#!/usr/bin/env python3
"""Disposable-copy integrity controls. Never edits the original sealed packet."""
import argparse,hashlib,json,os,pathlib,shutil,stat,subprocess,sys
sys.dont_write_bytecode=True

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    ans={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();n=str(p.relative_to(root));x={'mode':s.st_mode,'nlink':s.st_nlink}
        if p.is_symlink():x['target']=os.readlink(p)
        elif p.is_file():x.update(bytes=s.st_size,sha256=sha(p))
        ans[n]=x
    return ans

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--tree',required=True);a.add_argument('--output',required=True);args=a.parse_args()
    root=pathlib.Path(args.root).absolute();out=pathlib.Path(args.output).absolute();tree=pathlib.Path(args.tree).absolute()
    if out.parent!=root or out.exists():raise ValueError('output must be new file directly in author root')
    work=root/'scratch'/'copied-controls-r1'
    if work.exists():raise ValueError('refuse existing controls directory')
    before=snapshot(root);work.mkdir();copy=work/'copy';results=[]
    finalhash=sha(root/'FINAL.json');reporthash=sha(root/'REPORT.md')
    cases=['baseline','missing-final','wrong-final','wrong-report','payload-change','missing-payload','extra-file','extra-dir','directory-mode','symlink','hardlink','fifo','manifest-change','outside-report-change','public-report-change','source-register-change','canonical-change','wrong-tree','coherent-reseal']
    try:
      for case in cases:
        copy.mkdir();shutil.copytree(root/'packet',copy/'packet')
        for name in ['FINAL.json','MANIFEST.json','REPORT.md']:shutil.copy2(root/name,copy/name)
        p=copy/'packet';fh=finalhash;rh=reporthash;treepath=tree
        if case=='wrong-final':fh='0'*64
        elif case=='wrong-report':rh='0'*64
        elif case=='payload-change':(p/'public/other-screens.md').write_text('mutation\n')
        elif case=='missing-payload':(p/'public/other-screens.md').unlink()
        elif case=='extra-file':(p/'unexpected').write_text('extra')
        elif case=='extra-dir':(p/'empty-extra').mkdir()
        elif case=='directory-mode':(p/'public').chmod(0o700)
        elif case=='symlink':(p/'link').symlink_to('public/report.md')
        elif case=='hardlink':os.link(p/'public/report.md',p/'linked')
        elif case=='fifo':os.mkfifo(p/'pipe')
        elif case=='manifest-change':(copy/'MANIFEST.json').write_text('{}')
        elif case=='outside-report-change':(copy/'REPORT.md').write_text('changed')
        elif case=='public-report-change':(p/'public/report.md').write_text('changed')
        elif case=='source-register-change':(p/'public/canonical.json').write_text('[]')
        elif case=='canonical-change':
            x=json.loads((p/'public/canonical.json').read_text())[0];(p/x['local']).write_text('changed')
        elif case=='wrong-tree':treepath=copy/'wrong-tree.json';treepath.write_text('{}')
        elif case=='coherent-reseal':
            q=p/'public/other-screens.md';q.write_text('coherent change')
            m=json.loads((copy/'MANIFEST.json').read_text());m['files']['public/other-screens.md'].update(bytes=q.stat().st_size,sha256=sha(q));mp=copy/'MANIFEST.json';mp.write_text(json.dumps(m))
            f=json.loads((copy/'FINAL.json').read_text());f['manifest'].update(bytes=mp.stat().st_size,sha256=sha(mp));(copy/'FINAL.json').write_text(json.dumps(f))
        cmd=[sys.executable,'-B',str(p/'public/verify.py'),'--root',str(copy),'--reporthash',rh,'--tree',str(treepath)]
        if case!='missing-final':cmd+=['--finalhash',fh]
        snap=snapshot(copy);r=subprocess.run(cmd,capture_output=True,text=True,timeout=30);unchanged=snapshot(copy)==snap
        expected=case=='baseline';ok=(r.returncode==0)==expected and unchanged
        results.append({'case':case,'expected_accept':expected,'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'copy_unchanged':unchanged,'expected_outcome':ok})
        shutil.rmtree(copy)
      shutil.rmtree(work)
      unchanged=snapshot(root)==before
      result={'kind':'INTEGRITY_ONLY_NOT_MATHEMATICAL','final_sha256':finalhash,'outside_report_sha256':reporthash,'cases':results,'all_expected':all(x['expected_outcome'] for x in results),'whole_original_root_unchanged_before_receipt':unchanged,'before_snapshot_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()}
      out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'all_expected':result['all_expected'],'cases':len(results),'original_unchanged':unchanged}))
      if not result['all_expected'] or not unchanged:raise ValueError('control failure')
    finally:
      if work.exists():shutil.rmtree(work)
if __name__=='__main__':main()
