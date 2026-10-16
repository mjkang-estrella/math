#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Independent public-extraction and corruption controls; no author imports."""
from pathlib import Path
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile

OWN = Path(__file__).resolve().parents[1]
PACKAGE = OWN.parent/'kn-minus-edge-manuscript-r2'
PIN = '69a130a3e5d199277c2c7105b4e51c7a0fba972d7614aab86cc30236f515ac53'
ZIP = 'kn-minus-edge-manuscript-public.zip'
results = []


def run(root, label, args, expected, fragment=None, cwd=None):
    command=[sys.executable,'-B',str(root/'support/verify_package.py'),*args]
    proc=subprocess.run(command,cwd=cwd or OWN,capture_output=True,text=True,timeout=20,
                        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    row=dict(test=label,args=args,returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,
             expected_exit=expected,executed_from=str(cwd or OWN))
    results.append(row)
    (OWN/'receipts/verifier-cases.json').write_text(json.dumps(results,indent=2)+'\n')
    assert proc.returncode==expected,row
    assert proc.stdout.startswith('VERIFY PASSED' if expected==0 else 'VERIFY FAILED'),row
    assert not proc.stderr and 'Traceback' not in proc.stdout,row
    if fragment: assert fragment in proc.stdout,row


def edit_manifest(root,change):
    path=root/'public-manifest.json'; data=json.loads(path.read_bytes()); change(data)
    path.write_text(json.dumps(data))


def rehash_entry(root,name):
    data=(root/name).read_bytes()
    edit_manifest(root,lambda m: next(r for r in m['files'] if r['path']==name).update(
        bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))


def main():
    assert hashlib.sha256((PACKAGE/'public-manifest.json').read_bytes()).hexdigest()==PIN
    assert hashlib.sha256((PACKAGE/'support/verify_package.py').read_bytes()).hexdigest()=='3acff8ff4a3312245286c429e2ee00e2eb2c864877d3d160b85e4adf0e6f746a'
    run(PACKAGE,'full handoff',[],0)
    run(PACKAGE,'full handoff with fixed inputs and manifest anchor',['--with-inputs','--manifest-sha256',PIN],0)
    with tempfile.TemporaryDirectory(prefix='independent-verifier-',dir=OWN/'work') as scratch:
        temp=Path(scratch); clean=temp/'clean'
        with zipfile.ZipFile(PACKAGE/ZIP) as z:
            names=z.namelist()
            assert len(names)==len(set(names))==40
            assert not any(Path(n).is_absolute() or '..' in Path(n).parts for n in names)
            z.extractall(clean)
        assert not any((clean/n).exists() for n in [ZIP,'output-manifest.json','SHA256SUMS'])
        run(clean,'clean extraction without ZIP or private handoff records',['--public'],0)
        run(clean,'clean extraction with external anchor from unrelated cwd',['--public','--manifest-sha256',PIN],0,cwd=temp)
        run(clean,'wrong anchor',['--public','--manifest-sha256','f'*64],1,'external public-manifest hash mismatch')
        run(clean,'public mode refuses repository inputs',['--public','--with-inputs'],1,'requires full mode')
        run(clean,'full mode on public-only extraction',[],1,'missing file: '+ZIP)

        def case(label,mutate,fragment=None,args=None,full=False,expected=1):
            target=temp/f'case-{len(results):02d}'
            shutil.copytree(PACKAGE if full else clean,target)
            mutate(target)
            run(target,label,args if args is not None else ([] if full else ['--public']),expected,fragment)

        case('missing nested inherited source',lambda r:(r/'support/inherited/author/kn_minus_e_checks.py').unlink(),'missing file: support/inherited/author/kn_minus_e_checks.py')
        case('missing PDF',lambda r:(r/'main.pdf').unlink(),'missing file: main.pdf')
        case('one-byte PDF alteration',lambda r:(r/'main.pdf').write_bytes(b'!'+(r/'main.pdf').read_bytes()[1:]),'hash/size mismatch: main.pdf')
        case('PDF path replaced by directory',lambda r:((r/'main.pdf').unlink(),(r/'main.pdf').mkdir()),'missing file: main.pdf')
        case('unexpected deeply nested file',lambda r:((r/'extra').mkdir(),(r/'extra/secret.txt').write_text('control')),'file membership mismatch')
        case('extra empty directory is allowed by file-only contract',lambda r:(r/'extra-empty').mkdir(),expected=0)
        case('missing public manifest',lambda r:(r/'public-manifest.json').unlink(),'missing file: public-manifest.json')
        case('invalid UTF8 manifest',lambda r:(r/'public-manifest.json').write_bytes(b'\xff'),"VERIFY FAILED")
        case('malformed manifest checked against anchor before parse',lambda r:(r/'public-manifest.json').write_bytes(b'{'),
             'external public-manifest hash mismatch',args=['--public','--manifest-sha256',PIN])
        case('duplicate JSON key',lambda r:(r/'public-manifest.json').write_text('{"files":[],"files":[]}'),'duplicate JSON key')
        case('wrong top-level manifest type',lambda r:(r/'public-manifest.json').write_text('[]'),'VERIFY FAILED')
        case('wrong entries type',lambda r:edit_manifest(r,lambda m:m.update(files={})), 'entries must be a list')
        case('duplicate manifest entry',lambda r:edit_manifest(r,lambda m:m['files'].append(m['files'][0].copy())), 'duplicate manifest path')
        for label,key,value,fragment in [
            ('noncanonical path','path','./README.md','unsafe path'),
            ('parent traversal','path','../outside','unsafe path'),
            ('absolute path','path','/tmp/outside','unsafe path'),
            ('Windows separator','path','support\\bad.py','unsafe path'),
            ('nonstring path','path',7,'non-string path'),
            ('boolean byte size','bytes',True,'invalid byte size'),
            ('negative byte size','bytes',-1,'invalid byte size'),
            ('bad digest syntax','sha256','x'*64,'invalid hash')]:
            case(label,lambda r,k=key,v=value:edit_manifest(r,lambda m:m['files'][0].update({k:v})),fragment)

        case('payload symlink',lambda r:((r/'main.pdf').unlink(),(r/'main.pdf').symlink_to(clean/'main.pdf')), 'symlink: main.pdf')
        case('ancestor directory symlink',lambda r:(shutil.rmtree(r/'support/inherited'),(r/'support/inherited').symlink_to(clean/'support/inherited',target_is_directory=True)), 'symlink: support/inherited')
        case('unlisted dangling symlink',lambda r:(r/'dangling').symlink_to('nonexistent'),'symlink: dangling')
        case('unlisted FIFO',lambda r:os.mkfifo(r/'fifo-control'), 'unsupported entry: fifo-control')

        def change_payload_and_manifest(r):
            (r/'main.pdf').write_bytes((r/'main.pdf').read_bytes()+b'\nconsistency-control')
            rehash_entry(r,'main.pdf')
        case('self-consistent alteration without origin anchor',change_payload_and_manifest,expected=0)
        case('same alteration rejected by external anchor',change_payload_and_manifest,'external public-manifest hash mismatch',args=['--public','--manifest-sha256',PIN])

        def zip_mutation(r,kind):
            path=r/ZIP; out=io.BytesIO()
            with zipfile.ZipFile(path) as old, zipfile.ZipFile(out,'w') as new:
                for name in old.namelist():
                    data=old.read(name)
                    if kind=='payload' and name=='main.pdf': data+=b'\nzip-control'
                    new.writestr(name,data)
                if kind=='extra': new.writestr('extra.txt',b'extra')
            path.write_bytes(out.getvalue())
        case('ZIP payload inconsistent with public manifest',lambda r:zip_mutation(r,'payload'),'ZIP member mismatch: main.pdf',full=True)
        case('extra ZIP member',lambda r:zip_mutation(r,'extra'),'ZIP contents differ',full=True)
        case('invalid ZIP',lambda r:(r/ZIP).write_bytes(b'not-a-zip'),'VERIFY FAILED',full=True)
        for name in [ZIP,'output-manifest.json','SHA256SUMS']:
            case('full missing '+name,lambda r,n=name:(r/n).unlink(),'VERIFY FAILED',full=True)
        case('duplicate checksum path',lambda r:(r/'SHA256SUMS').write_bytes((r/'SHA256SUMS').read_bytes()*2),'duplicate checksum path',full=True)
        case('malformed checksum line',lambda r:(r/'SHA256SUMS').write_text('malformed\n'),'VERIFY FAILED',full=True)
        case('bad handoff output entry',lambda r:(r/'output-manifest.json').write_text('{"files":[{}]}'),'VERIFY FAILED',full=True)
    summary=dict(status='PASS',scenarios=len(results),all_expected_outcomes=True,
                 clean_public_members=40,clean_public_payload_entries=39,
                 original_frozen_files_not_modified=True,
                 semantic_limits=['Unanchored mode checks consistency; a self-consistent mutation passes by design. External authentication rejects it.',
                                  'Exact membership is for files, not empty directories.'],
                 command=[sys.executable,'-B',str(Path(__file__).resolve())],python=sys.version)
    (OWN/'receipts/verifier-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
