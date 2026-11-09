"""Copied integrity controls under the assigned root only. Original code, MIT."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(p):return {str(f.relative_to(p)):sha(f) for f in p.rglob('*') if f.is_file() and not f.is_symlink()}
def main():
    ap=argparse.ArgumentParser()
    for n in ('root','final-sha256','manifest-sha256','report-sha256','original-project'):ap.add_argument('--'+n,required=True)
    a=ap.parse_args();r=Path(a.root).resolve();work=r/'work/private-controls';work.mkdir(parents=True,exist_ok=True)
    fixture=work/'fixture'
    if fixture.exists():raise SystemExit('Use a fresh controls directory; no overwrite')
    fixture.mkdir();shutil.copytree(r/'packet',fixture/'packet');shutil.copy2(r/'REPORT.md',fixture/'REPORT.md')
    original_before=snapshot(r/'packet');results=[]
    cmd=[sys.executable,'-B',str(r/'packet/public/verify.py'),'--root',str(fixture),'--final-sha256',a.final_sha256,'--manifest-sha256',a.manifest_sha256,'--report-sha256',a.report_sha256,'--original-project',a.original_project]
    def run(name,expect,command=None):
        before=snapshot(fixture);z=subprocess.run(command or cmd,capture_output=True,text=True);after=snapshot(fixture)
        if before!=after:raise RuntimeError('verifier wrote fixture')
        if (z.returncode==0)!=expect:raise RuntimeError(name+': unexpected outcome '+z.stdout+z.stderr)
        results.append({'case':name,'accepted':z.returncode==0,'expected':expect,'fixture_unchanged_by_verifier':True})
    run('baseline',True)
    p=fixture/'packet/public/DERIVATION.md';old=p.read_bytes();p.write_bytes(old+b'\nmutation\n');run('payload',False);p.write_bytes(old)
    p.unlink();run('missing',False);p.write_bytes(old)
    extra=fixture/'packet/extra';extra.mkdir();run('extra-directory',False);extra.rmdir()
    p.unlink();p.symlink_to(r/'packet/public/DERIVATION.md');run('symlink',False);p.unlink();p.write_bytes(old)
    report=fixture/'REPORT.md';rold=report.read_bytes();report.write_bytes(rold+b'changed');run('outside-report',False);report.write_bytes(rold)
    mf=fixture/'packet/MANIFEST.json';ff=fixture/'packet/FINAL.json';mo=mf.read_bytes();fo=ff.read_bytes();mf.write_bytes(mo+b' ');fj=json.loads(fo);fj['manifest_sha256']=sha(mf);ff.write_text(json.dumps(fj));run('forged-internal-reseal',False);mf.write_bytes(mo);ff.write_bytes(fo)
    bad=cmd.copy();bad[bad.index('--final-sha256')+1]='0'*64;run('wrong-detached-anchor',False,bad)
    run('restored',True)
    if snapshot(r/'packet')!=original_before:raise RuntimeError('original packet changed')
    out={'artifact_only':True,'cases':results,'original_packet_unchanged':True}
    (r/'work/controls-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'artifact_only':True,'cases':len(results),'status':'expected outcomes','original_packet_unchanged':True}))
if __name__=='__main__':main()
