#!/usr/bin/env python3
"""Disposable copied controls. No resealing, no original payload writes."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root,excluded):
    out={}
    for here,ds,fs in os.walk(root,followlinks=False):
        ds[:]=[d for d in ds if Path(here)/d!=excluded]
        for name in ds+fs:
            p=Path(here)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
            out[rel]=[s.st_mode,s.st_nlink,s.st_size if stat.S_ISREG(s.st_mode) else None,sha(p) if stat.S_ISREG(s.st_mode) else None]
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--tree',required=True);a=ap.parse_args()
    root=Path(a.root).absolute();tree=Path(a.tree).absolute()
    work=Path(tempfile.mkdtemp(prefix='.controls-',dir=root));before=snapshot(root,work);records=[]
    def invoke(c,fh=None,rh=None,tp=None,omit=False):
        cmd=[sys.executable,'-B',str(c/'verify.py'),'--root',str(c),'--reporthash',rh or a.reporthash,'--tree',str(tp or tree)]
        if not omit:cmd+=['--finalhash',fh or a.finalhash]
        return subprocess.run(cmd,capture_output=True,text=True,timeout=30)
    def case(name,mutate=None,expect=True,**kw):
        c=work/name;c.mkdir();shutil.copytree(root/'packet',c/'packet')
        for fn in ['FINAL.json','MANIFEST.json','REPORT.md','verify.py','run_controls.py']:shutil.copyfile(root/fn,c/fn)
        if mutate:mutate(c)
        cp=invoke(c,**kw);ok=(cp.returncode==0)==expect
        records.append({'case':name,'expected_accept':expect,'observed_exit':cp.returncode,'matched_expectation':ok,'output':(cp.stdout+cp.stderr).strip()})
        if not ok:raise RuntimeError('unexpected control '+name)
    def change(c,path):p=c/path;p.write_bytes(p.read_bytes()+b'\nCHANGED\n')
    try:
        cp=invoke(root)
        if cp.returncode:raise RuntimeError(cp.stderr)
        case('baseline')
        case('wrong-final',expect=False,fh='0'*64)
        case('wrong-report',expect=False,rh='0'*64)
        case('missing-detached-final',expect=False,omit=True)
        case('payload-change',lambda c:change(c,'packet/public/report.md'),False)
        case('missing-payload',lambda c:(c/'packet/public/report.md').unlink(),False)
        case('extra-payload',lambda c:(c/'packet/NEWTEST').write_text('extra'),False)
        case('extra-empty-directory',lambda c:(c/'packet/NEWTEST').mkdir(),False)
        case('symlink',lambda c:(c/'packet/NEWTEST').symlink_to(c/'REPORT.md'),False)
        case('hardlink',lambda c:os.link(c/'packet/public/report.md',c/'packet/NEWTEST'),False)
        case('fifo',lambda c:os.mkfifo(c/'packet/NEWTEST'),False)
        case('manifest-change',lambda c:change(c,'MANIFEST.json'),False)
        case('verifier-change',lambda c:change(c,'verify.py'),False)
        case('controls-program-change',lambda c:change(c,'run_controls.py'),False)
        case('report-change',lambda c:change(c,'REPORT.md'),False)
        def reseal(c):
            p=c/'packet/public/report.md';p.write_text('coherent altered report\n')
            m=json.loads((c/'MANIFEST.json').read_text())
            for x in m['files']:
                if x['path']=='public/report.md':x.update(bytes=p.stat().st_size,sha256=sha(p))
            (c/'MANIFEST.json').write_text(json.dumps(m))
            f=json.loads((c/'FINAL.json').read_text());f['manifest_sha256']=sha(c/'MANIFEST.json');(c/'FINAL.json').write_text(json.dumps(f))
        case('coherent-reseal-with-old-detached-anchor',reseal,False)
        badtree=work/'bad-tree.json';badtree.write_text('{}\n');case('wrong-external-tree',expect=False,tp=badtree)
        after=snapshot(root,work)
        if before!=after:raise RuntimeError('original root changed')
        cp=invoke(root)
        if cp.returncode:raise RuntimeError('final original verification failed: '+cp.stderr)
        result={'controls':records,'all_expected':True,'original_root_unchanged':True,'original_snapshot_entries':len(before),'mathematical_gate':False,'finalhash':a.finalhash,'reporthash':a.reporthash}
    finally:shutil.rmtree(work)
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
