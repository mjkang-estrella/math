#!/usr/bin/env python3
"""Parent R3 regression checks in disposable extractions; never edit frozen inputs."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

PARENT = Path(__file__).resolve().parent
PACKAGE = PARENT.parent / 'kn-minus-edge-manuscript-r2'
REVIEW = PARENT.parent / 'kn-minus-edge-manuscript-review-r1'
OLD = PARENT.parent / 'kn-minus-edge-manuscript'
SHA = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
results = []


def run(base, label, args, success, fragment=None):
    proc = subprocess.run([sys.executable, '-B', str(base / 'support/verify_package.py'), *args],
                          capture_output=True, text=True, timeout=30)
    assert proc.returncode == (0 if success else 1), (label, proc.stdout, proc.stderr)
    assert proc.stdout.startswith('VERIFY PASSED' if success else 'VERIFY FAILED'), label
    assert not proc.stderr and 'Traceback' not in proc.stdout, label
    if fragment:
        assert fragment in proc.stdout, (label, proc.stdout)
    results.append(dict(test=label,returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr))


def main():
    before = {str(f): SHA(f) for f in PACKAGE.rglob('*') if f.is_file()}
    manifest_hash = SHA(PACKAGE / 'public-manifest.json')
    run(PACKAGE, 'full handoff with repository inputs', ['--with-inputs', '--manifest-sha256', manifest_hash], True)
    with tempfile.TemporaryDirectory(prefix='kn-manuscript-r2-') as temp:
        root = Path(temp)
        clean = root / 'clean'
        with zipfile.ZipFile(PACKAGE / 'kn-minus-edge-manuscript-public.zip') as archive:
            for name in archive.namelist():
                assert not Path(name).is_absolute() and '..' not in Path(name).parts
            archive.extractall(clean)
        assert not any((clean / name).exists() for name in ['output-manifest.json','SHA256SUMS','kn-minus-edge-manuscript-public.zip'])
        run(clean, 'public extraction without handoff files', ['--public'], True)
        run(clean, 'public extraction trusted manifest', ['--public','--manifest-sha256',manifest_hash], True)
        run(clean, 'wrong external anchor', ['--public','--manifest-sha256','0'*64], False, 'external public-manifest hash mismatch')
        run(clean, 'full mode on public extraction', [], False, 'missing file: kn-minus-edge-manuscript-public.zip')
        run(clean, 'incompatible public and input modes', ['--public','--with-inputs'], False, '--with-inputs requires full mode')
        mutations = [
            ('missing PDF', lambda x: (x/'main.pdf').unlink(), 'missing file: main.pdf'),
            ('altered PDF', lambda x: (x/'main.pdf').write_bytes((x/'main.pdf').read_bytes()+b'\nchanged'), 'hash/size mismatch: main.pdf'),
            ('unlisted file', lambda x: (x/'extra.txt').write_text('extra'), 'file membership mismatch'),
            ('missing manifest', lambda x: (x/'public-manifest.json').unlink(), 'missing file: public-manifest.json'),
            ('malformed manifest', lambda x: (x/'public-manifest.json').write_text('{'), None),
            ('duplicate JSON key', lambda x: (x/'public-manifest.json').write_text('{"files":[],"files":[]}'), 'duplicate JSON key'),
        ]
        def alter_entry(x, change):
            file=x/'public-manifest.json'; data=json.loads(file.read_text());change(data['files']);file.write_text(json.dumps(data))
        mutations += [
            ('duplicate manifest path', lambda x: alter_entry(x, lambda items: items.append(dict(items[0]))), 'duplicate manifest path'),
            ('parent traversal', lambda x: alter_entry(x, lambda items: items[0].update(path='../outside')), 'unsafe path'),
            ('absolute path', lambda x: alter_entry(x, lambda items: items[0].update(path='/tmp/outside')), 'unsafe path'),
        ]
        def symlink_pdf(x):
            (x/'main.pdf').unlink();(x/'main.pdf').symlink_to(clean/'main.pdf')
        mutations.append(('symlink payload', symlink_pdf, 'symlink: main.pdf'))
        for i,(label,mutate,fragment) in enumerate(mutations):
            target=root/f'control-{i}';shutil.copytree(clean,target);mutate(target)
            run(target,label,['--public'],False,fragment)
        malformed=root/'control-anchor-before-parse';shutil.copytree(clean,malformed)
        (malformed/'public-manifest.json').write_text('{')
        run(malformed,'authenticate before JSON parsing',['--public','--manifest-sha256',manifest_hash],False,'external public-manifest hash mismatch')
        for i,name in enumerate(['kn-minus-edge-manuscript-public.zip','output-manifest.json','SHA256SUMS']):
            target=root/f'full-missing-{i}';shutil.copytree(PACKAGE,target);(target/name).unlink()
            run(target,f'full missing {name}',[],False,
                'handoff file membership mismatch' if name=='SHA256SUMS' else f'missing file: {name}')

    a=(OLD/'main.tex').read_text();b=(PACKAGE/'main.tex').read_text()
    start='\\section{Conventions and upstream statements}';end='\\section{Novelty boundary}'
    assert a[a.index(start):a.index(end)] == b[b.index(start):b.index(end)]
    for env in ['maintheorem','maincorollary']:
        pat=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
        assert re.findall(pat,a,re.S)==re.findall(pat,b,re.S)
    for filename in ['release_checks.py','run_all.py']:
        assert (OLD/'support'/filename).read_bytes()==(PACKAGE/'support'/filename).read_bytes()
    for f in (OLD/'support/inherited').rglob('*'):
        if f.is_file(): assert f.read_bytes()==(PACKAGE/f.relative_to(OLD)).read_bytes()
    algebra=subprocess.run([sys.executable,'-B',str(REVIEW/'checks/independent_algebra.py')],capture_output=True,text=True,timeout=30)
    assert algebra.returncode==0 and algebra.stdout=='independent algebra PASS\n' and not algebra.stderr
    for name,h in before.items(): assert SHA(Path(name))==h,name
    protected=json.loads((PARENT/'manuscript-r2-before.json').read_text())
    for name,h in protected.items(): assert SHA(Path(name))==h,name
    receipt=dict(status='PASS_REVISION_CHECKS',public_manifest_sha256=manifest_hash,verifier_sha256=SHA(PACKAGE/'support/verify_package.py'),pdf_sha256=SHA(PACKAGE/'main.pdf'),output_manifest_sha256=SHA(PACKAGE/'output-manifest.json'),zip_sha256=SHA(PACKAGE/'kn-minus-edge-manuscript-public.zip'),tests=results,proof_sections_2_through_6_unchanged=True,full_theorem_and_corollary_statements_unchanged=True,mathematical_checkers_unchanged=True,independent_algebra=algebra.stdout,protected_old_files_unchanged=len(protected),new_package_files_unchanged_during_checks=len(before),limits=['Parent revision checks, not a fresh independent full mathematical review.','No Lean rebuild or long modular rerun; inherited receipts explicitly identified.','No acceptance or publication.'])
    (PARENT/'manuscript-r2-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='tests'},indent=2))
    print('Verifier scenarios:',len(results))


if __name__=='__main__':
    main()
