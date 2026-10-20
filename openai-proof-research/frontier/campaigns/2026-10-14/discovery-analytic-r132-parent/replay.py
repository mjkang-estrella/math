#!/usr/bin/env python3
"""Detached parent intake of analytic132; artifact checks only."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
FINAL='44b08b8e400fa6477d1ab1e1f918e3d23098d60beb19b02112f29a2d8a12a366'
MANIFEST='594c1cad6d394b851b9468c7b002b84a1469753a033633a6a44445587798a44f'
REPORT='a516626c4d5585f1b19e892138f592846337727566576e01659f546e5d9d4ae9'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();r=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode):r += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode):r += [os.readlink(p)]
        out[p.relative_to(root).as_posix()]=r
    return out
def run(args,cwd):
    r=subprocess.run([sys.executable,'-B',*args],cwd=cwd,capture_output=True,text=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def main():
    parent=Path(__file__).resolve().parent;campaign=parent.parent;repo=campaign.parents[2]
    author=campaign/'fresh-analytic-discovery-r132'
    assert sha(author/'FINAL.json')==FINAL and sha(author/'packet/MANIFEST.json')==MANIFEST
    assert sha(author/'REPORT.md')==REPORT
    fin=json.loads((author/'FINAL.json').read_text());deps=fin['external_inputs_sha256']
    before={'author':snapshot(author),'external':{n:sha(repo/n) for n in deps}}
    assert before['external']==deps
    tree={e['path']:e for e in json.loads((repo/'sources/preprints-tree.json').read_text())['tree']}
    reg=json.loads((author/'packet/private/registers/upstream-register.json').read_text())
    for r in reg:
        e=tree[r['path']];data=(author/'packet/private/upstream'/r['path']).read_bytes()
        assert e['type']=='blob' and r['size']==len(data)==e['size']
        assert r['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert r['sha256']==hashlib.sha256(data).hexdigest()
        assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
    common=['--root','.', '--manifest-sha256',MANIFEST,'--final-sha256',FINAL,
            '--report-sha256',REPORT,'--project-root',str(repo)]
    original=run(['packet/public/verify.py',*common],author)
    with tempfile.TemporaryDirectory(prefix='r132-intake-',dir=parent) as td:
        copy=Path(td)/'author';shutil.copytree(author,copy,symlinks=True)
        verify=run(['packet/public/verify.py',*common],copy)
        bad=list(common);bad[bad.index('--final-sha256')+1]='0'*64
        wrong=run(['packet/public/verify.py',*bad],copy)
        tempbase=Path(td)/'controls';tempbase.mkdir()
        controls=run(['packet/public/controls.py',str(copy),MANIFEST,FINAL,REPORT,str(tempbase)],copy)
        receipt=json.loads(controls['stdout'])
    after={'author':snapshot(author),'external':{n:sha(repo/n) for n in deps}}
    ok=(original['exit']==0 and verify['exit']==0 and wrong['exit']!=0 and controls['exit']==0
        and receipt['all_as_expected'] and before==after)
    out={'kind':'PARENT_ARTIFACT_INTAKE_ONLY','mathematical_gate':False,
         'detached_anchors':{'final':FINAL,'manifest':MANIFEST,'report':REPORT},
         'original_verify':original,'copy_verify':verify,'wrong_final':wrong,
         'copied_controls':controls,'control_receipt':receipt,
         'canonical_source_records_authenticated':len(reg),'external_inputs':len(deps),
         'actual_author_unchanged':before['author']==after['author'],
         'actual_external_inputs_unchanged':before['external']==after['external'],
         'control_limit':'Provided copied controls check internal bytes/inventory/anchors; external bindings are separately checked by parent baseline verifier and full before/after dependency hashes.',
         'all_expected':ok}
    (parent/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['all_expected','canonical_source_records_authenticated',
                                      'external_inputs','actual_author_unchanged','actual_external_inputs_unchanged']}))
    print('Copied controls:',receipt['cases'])
    return 0 if ok else 1
if __name__=='__main__':sys.exit(main())
