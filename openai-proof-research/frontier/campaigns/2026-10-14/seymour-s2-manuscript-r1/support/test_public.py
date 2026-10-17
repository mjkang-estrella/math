"""Local release tests from clean extraction, including corruption controls. MIT."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile
R=Path(__file__).resolve().parents[1]
results={}
with tempfile.TemporaryDirectory(dir=R/'tmp',prefix='public-test-') as tmp:
    T=Path(tmp)
    with zipfile.ZipFile(R/'seymour-s2-public.zip') as z:z.extractall(T)
    def run(script,expect_success=True,args=[]):
        p=subprocess.run([sys.executable,'-B',str(T/script),*args],cwd=T,capture_output=True,text=True)
        if (p.returncode==0)!=expect_success:raise RuntimeError(str((script,p.returncode,p.stdout,p.stderr)))
        return {'exit_code':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()}
    h=hashlib.sha256((T/'public-manifest.json').read_bytes()).hexdigest()
    results['clean_integrity']=run('support/verify_package.py',args=['--manifest-sha256',h])
    results['clean_finite_checks']=run('support/run_checks.py')
    # Rerunning checks must not mutate frozen payloads.
    results['integrity_after_checks']=run('support/verify_package.py')
    f=T/'main.tex';old=f.read_bytes();f.write_bytes(old+b'\n% deliberate mutation\n')
    results['changed_payload_rejected']=run('support/verify_package.py',False);f.write_bytes(old)
    f=T/'support/inherited/author.py';old=f.read_bytes();f.unlink()
    results['missing_checker_integrity_rejected']=run('support/verify_package.py',False)
    results['missing_checker_execution_rejected']=run('support/run_checks.py',False);f.write_bytes(old)
    f=T/'extra.txt';f.write_text('extra')
    results['extra_payload_rejected']=run('support/verify_package.py',False);f.unlink()
    manifest=T/'public-manifest.json';old=manifest.read_bytes();m=json.loads(old)
    key='support/inherited/reviewer.py';f=T/key;checker=f.read_bytes();f.unlink()
    m['files']=[r for r in m['files'] if r['path']!=key];manifest.write_text(json.dumps(m))
    results['missing_required_anchor_even_with_rewritten_manifest_rejected']=run('support/verify_package.py',False)
    manifest.write_bytes(old);f.write_bytes(checker)
    results['wrong_external_manifest_hash_rejected']=run('support/verify_package.py',False,args=['--manifest-sha256','0'*64])
    results['restored_integrity']=run('support/verify_package.py')
results['status']='PASS_RELEASE_TESTS_ONLY'
results['public_manifest_sha256']=h
results['meaning']='Clean extraction integrity and finite diagnostics, with deliberate corruption controls; no mathematical or acceptance gate awarded.'
(R/'checks/public-extraction-tests.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({'status':results['status'],'controls':len(results)-3,'manifest_sha256':h}))
