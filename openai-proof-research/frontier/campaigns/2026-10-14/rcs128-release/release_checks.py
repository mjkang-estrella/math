#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exercise portable RCS128 release verification in a NEW disposable work directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import zipfile

HERE=Path(__file__).resolve().parent

def sha(data):return hashlib.sha256(data).hexdigest()
def dump(data):return (json.dumps(data,indent=2)+'\n').encode()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive',type=Path,required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--gate-sha256',required=True)
    ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--tectonic',type=Path,required=True)
    a=ap.parse_args();archive=a.archive.resolve();work=a.work.resolve()
    work.mkdir(parents=True,exist_ok=False)
    cases=[]
    def run(label,command,ok=True,reason=None,cwd=None):
        result=subprocess.run(command,cwd=cwd,capture_output=True,text=True)
        (work/(label+'.stdout')).write_text(result.stdout)
        (work/(label+'.stderr')).write_text(result.stderr)
        assert (result.returncode==0)==ok,(label,result.returncode,result.stdout,result.stderr)
        if reason:assert reason in result.stdout+result.stderr,(label,'missing expected reason')
        cases.append({'case':label,'exit_code':result.returncode,'expected':'ACCEPT' if ok else 'REJECT','reason_checked':reason,'stdout_sha256':sha(result.stdout.encode()),'stderr_sha256':sha(result.stderr.encode())})
        return result
    def verify(label,path,ok=True,reason=None,m=None,g=None,helper=None):
        return run(label,[sys.executable,'-B',str(helper or HERE/'verify_bundle.py'),str(path),'--manifest-sha256',m or a.manifest_sha256,'--gate-sha256',g or a.gate_sha256],ok,reason)
    verify('zip-positive',archive)
    clean=work/'clean';clean.mkdir()
    with zipfile.ZipFile(archive) as z:z.extractall(clean)
    verify('clean-positive',clean,helper=clean/'verify_bundle.py')
    run('reassemble',[sys.executable,'-B',str(clean/'assemble.py'),'--gate',str(clean/'FINAL-GATE.json'),'--gate-sha256',a.gate_sha256,'--output',str(work/'reassembled.zip')])
    assert (work/'reassembled.zip').read_bytes()==archive.read_bytes(),'nonidentical reassembly'
    verify('reassembled-positive',work/'reassembled.zip',helper=clean/'verify_bundle.py')
    verify('wrong-manifest',clean,False,'external manifest hash mismatch',m='0'*64)
    verify('wrong-gate-hash',clean,False,'manifest gate mismatch',g='0'*64)
    file=clean/'README.md';original=file.read_bytes()
    file.write_bytes(original+b'CORRUPTED\n');verify('changed-file',clean,False,'size/hash mismatch');file.write_bytes(original)
    file.unlink();verify('missing-file',clean,False);file.write_bytes(original)
    extra=clean/'EXTRA.txt';extra.write_text('not part of archive');verify('extra-file',clean,False,'exact membership mismatch');extra.unlink()
    empty=clean/'empty-extra-directory';empty.mkdir();verify('extra-directory',clean,False,'exact directory membership mismatch');empty.rmdir()
    file.unlink();file.symlink_to('RIGHTS.md');verify('symlink-file',clean,False,'symlink entry');file.unlink();file.write_bytes(original)
    hard=clean/'hardlink';os.link(file,hard);verify('hardlink-file',clean,False,'hardlinked entry');hard.unlink()
    fifo=clean/'fifo';os.mkfifo(fifo);verify('special-file',clean,False,'unsupported entry');fifo.unlink()
    link=work/'symlink-root';link.symlink_to(clean,target_is_directory=True);verify('symlink-root',link,False,'symlink root');link.unlink()
    gate_bytes=(clean/'FINAL-GATE.json').read_bytes();manifest_bytes=(clean/'BUNDLE-MANIFEST.json').read_bytes()
    gate=json.loads(gate_bytes)
    pending=dict(gate,status='PENDING');pending_raw=dump(pending);pending_path=work/'pending-gate.json';pending_path.write_bytes(pending_raw)
    run('pending-assembly',[sys.executable,'-B',str(clean/'assemble.py'),'--gate',str(pending_path),'--gate-sha256',sha(pending_raw),'--output',str(work/'must-not-exist.zip')],False,'final independent gate still pending')
    assert not (work/'must-not-exist.zip').exists()
    def semantic_case(label,modified,reason):
        raw=dump(modified);mh=json.loads(manifest_bytes);mh['gate_sha256']=sha(raw)
        for row in mh['files']:
            if row['path']=='FINAL-GATE.json':row.update(bytes=len(raw),sha256=sha(raw))
        manifest=dump(mh)
        (clean/'FINAL-GATE.json').write_bytes(raw);(clean/'BUNDLE-MANIFEST.json').write_bytes(manifest)
        verify(label,clean,False,reason,m=sha(manifest),g=sha(raw))
        (clean/'FINAL-GATE.json').write_bytes(gate_bytes);(clean/'BUNDLE-MANIFEST.json').write_bytes(manifest_bytes)
    semantic_case('pending-portable-verifier',pending,'final independent gate still pending')
    changed=json.loads(gate_bytes);changed['verdicts']['formal']='PENDING';semantic_case('wrong-verdict',changed,'required verdicts missing or different')
    changed=json.loads(gate_bytes);changed['full_RCS128_formalized']=True;semantic_case('false-full-formal',changed,'unsupported full formal claim')
    changed=json.loads(gate_bytes);changed['anchors']['rcs128-proof-r1']['sha256']='0'*64;semantic_case('wrong-dependency-anchor',changed,'gate dependency anchors changed')
    # A ZIP symlink must be rejected before content validation.
    with zipfile.ZipFile(archive) as src,zipfile.ZipFile(work/'symlink.zip','w') as dst:
        for info in src.infolist():
            data=src.read(info.filename)
            if info.filename=='README.md':info.external_attr=0o120777<<16;data=b'RIGHTS.md'
            dst.writestr(info,data)
    verify('symlink-zip',work/'symlink.zip',False,'non-file ZIP member')
    verify('restored-clean',clean,helper=clean/'verify_bundle.py')
    manuscript=clean/'frontier/campaigns/2026-10-14/rcs128-manuscript-r1'
    build=work/'pdf-rebuild'
    source=work/'pdf-source';shutil.copytree(manuscript/'public',source)
    run('pdf-rebuild',[sys.executable,'-I','-B',str(source/'build.py'),'--output',str(build),'--tectonic',str(a.tectonic.resolve())])
    pdf=build/'article.pdf'
    assert pdf.read_bytes()==(manuscript/'public/output/pdf/rcs128.pdf').read_bytes(),'PDF byte drift'
    rendered=work/'rendered';rendered.mkdir()
    run('pdf-render',['pdftoppm','-png','-r','110',str(pdf),str(rendered/'page')])
    visual=json.loads((manuscript/'validation/page-inspection.json').read_text())
    assert visual['pdf_sha256']==sha(pdf.read_bytes()) and visual['method'],'visual PDF identity'
    expected_pages=sorted(visual['results'],key=lambda row:row['page'])
    fresh_pages=sorted(rendered.glob('page-*.png'))
    assert len(expected_pages)==len(fresh_pages)==visual['pages']==17,'page count drift'
    pages=[]
    for n,(row,path) in enumerate(zip(expected_pages,fresh_pages),1):
        assert row['page']==n and row['status']=='PASS','missing inspection record'
        assert path.name==Path(row['image']).name,'page inventory drift'
        assert sha(path.read_bytes())==row['sha256'],('render hash drift',n)
        pages.append({'page':n,'sha256':sha(path.read_bytes()),'identical_to_reviewed_page':True,'identity_method':'SHA256 matches sealed author visual record, also individually inspected by root'})
    for name in ['build-receipt.json','article.log','build.stdout','build.stderr']:shutil.copyfile(build/name,work/('pdf-'+name))
    receipt={'status':'PASS_RELEASE_CHECKS','archive_sha256':sha(archive.read_bytes()),'manifest_sha256':a.manifest_sha256,'gate_sha256':a.gate_sha256,'deterministic_reassembly_byte_identical':True,'fresh_pdf_sha256':sha(pdf.read_bytes()),'fresh_render_pages':pages,'cases':cases,'Lean_rebuilt':False,'no_new_visual_claim':'All fresh page hashes match the sealed individually inspected manuscript page records.','scope':'Integrity/reproduction checks only; no theorem/priority/acceptance/publication inference.'}
    (work/'receipt.json').write_bytes(dump(receipt))
    shutil.rmtree(clean);shutil.rmtree(build);shutil.rmtree(source);shutil.rmtree(rendered)
    (work/'reassembled.zip').unlink();(work/'symlink.zip').unlink()
    print(json.dumps({'status':receipt['status'],'cases':len(cases),'pdf_sha256':receipt['fresh_pdf_sha256'],'archive_sha256':receipt['archive_sha256']},indent=2))

if __name__=='__main__':main()
