#!/usr/bin/env python3
"""Detached parent intake of analytic133; artifact checks only."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
FINAL='4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09'
MANIFEST='9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324'
REPORT='3659f82ea364b41303f4097e7df0d12ef380cab5a2d43b0f6bc39ed1405d49fd'
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
    author=campaign/'fresh-analytic-discovery-r133'
    assert sha(author/'FINAL.json')==FINAL and sha(author/'packet/MANIFEST.json')==MANIFEST
    assert sha(author/'REPORT.md')==REPORT
    fin=json.loads((author/'FINAL.json').read_text());deps=fin['external_inputs_sha256']
    before={'author':snapshot(author),'external':{n:sha(repo/n) for n in deps}}
    assert before['external']==deps
    tree={e['path']:e for e in json.loads((repo/'sources/preprints-tree.json').read_text())['tree']}
    manifest=json.loads((author/'packet/MANIFEST.json').read_text())
    scope='86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354'
    assert sha(author/'packet/public/FROZEN-THEOREM.md')==scope
    assert sha(repo/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    reg=[]
    for rel in manifest['files']:
        prefix='packet/private/upstream/'
        if not rel.startswith(prefix):continue
        path=rel[len(prefix):];data=(author/rel).read_bytes();e=tree[path]
        assert e['type']=='blob' and len(data)==e['size']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
        reg.append({'path':path,'git_blob':e['sha'],'canonical_url':'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,'sha256':sha(author/rel)})
    common=['--root','.', '--manifest-sha256',MANIFEST,'--final-sha256',FINAL,
            '--report-sha256',REPORT,'--project-root',str(repo)]
    original=run(['packet/public/verify.py',*common],author)
    with tempfile.TemporaryDirectory(prefix='r133-intake-',dir=parent) as td:
        copy=Path(td)/'author';shutil.copytree(author,copy,symlinks=True)
        verify=run(['packet/public/verify.py',*common],copy)
        bad=list(common);bad[bad.index('--final-sha256')+1]='0'*64
        wrong=run(['packet/public/verify.py',*bad],copy)
        tempbase=Path(td)/'controls';tempbase.mkdir()
        receipt_path=tempbase/'receipt.json'
        controls=run(['packet/public/controls.py','--root','.', '--manifest-sha256',MANIFEST,'--final-sha256',FINAL,'--report-sha256',REPORT,'--out',str(receipt_path)],copy)
        receipt=json.loads(receipt_path.read_text())
    after={'author':snapshot(author),'external':{n:sha(repo/n) for n in deps}}
    ok=(original['exit']==0 and verify['exit']==0 and wrong['exit']!=0 and controls['exit']==0
        and receipt['all_as_expected'] and before==after)
    out={'kind':'PARENT_ARTIFACT_INTAKE_ONLY','mathematical_gate':False,
         'detached_anchors':{'final':FINAL,'manifest':MANIFEST,'report':REPORT},
         'original_verify':original,'copy_verify':verify,'wrong_final':wrong,
         'copied_controls':controls,'control_receipt':receipt,
         'canonical_source_records_authenticated':len(reg),'canonical_sources':reg,'frozen_scope_sha256':scope,'external_inputs':len(deps),
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
