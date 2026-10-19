#!/usr/bin/env python3
"""MIT. Mutates disposable copies only; requires detached final manifest anchor."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    dirs={};files={}
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix();s=p.lstat()
        if stat.S_ISDIR(s.st_mode):dirs[rel]=stat.S_IMODE(s.st_mode)
        elif stat.S_ISREG(s.st_mode) and rel!='manifest.json':
            files[rel]={'sha256':digest(p),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode)}
    return dirs,files

def reseal_copy(root):
    p=root/'manifest.json';m=json.loads(p.read_text());m['directories'],m['files']=inventory(root)
    p.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');return digest(p)

def mutate_json(p,fn):
    x=json.loads(p.read_text());fn(x);p.write_text(json.dumps(x,indent=2)+'\n')

def main():
    if len(sys.argv)!=3:raise SystemExit('usage: copied-controls.py PACKET DETACHED_FINALHASH')
    source=Path(sys.argv[1]).absolute();anchor=sys.argv[2]
    if digest(source/'manifest.json')!=anchor:raise SystemExit('external-anchor-mismatch')
    original=inventory(source); parent=source.parent/'control-copies';parent.mkdir(exist_ok=True)
    cases=[]
    def trial(name,change,reason=None,reanchor=False,wrong=None):
        with tempfile.TemporaryDirectory(prefix=name+'-',dir=parent) as tmp:
            dst=Path(tmp)/'packet';shutil.copytree(source,dst)
            if change:change(dst)
            a=reseal_copy(dst) if reanchor else (wrong or anchor)
            command=[sys.executable,'-B',str(dst/'public/verify.py'),str(dst),a]
            if name=='missing-external-anchor':command=command[:-1]
            before=inventory(dst)
            r=subprocess.run(command,capture_output=True,text=True,timeout=30)
            after=inventory(dst)
            passed=(r.returncode==0) if reason is None else (r.returncode!=0 and reason in r.stderr)
            if reason is None:passed=passed and before==after
            cases.append({'case':name,'passed':passed,'expected_reason':reason,'reanchored_copy':reanchor,
                          'base_final_anchor':anchor,'used_anchor':a,'returncode':r.returncode,
                          'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'read_only_inventory':before==after})
            if not passed:raise RuntimeError(json.dumps(cases[-1]))
    trial('positive',None)
    trial('wrong-anchor',None,'external-anchor-mismatch',wrong='0'*64)
    trial('missing-external-anchor',None,'usage: verify.py')
    trial('modified-report',lambda d:(d/'public/research-report.md').write_text('corrupt\n'),'file-integrity:public/research-report.md')
    trial('missing-file',lambda d:(d/'public/operation-comparison.md').unlink(),'file-inventory')
    trial('extra-file',lambda d:(d/'extra.txt').write_text('x'),'file-inventory')
    trial('extra-directory',lambda d:(d/'extra-empty').mkdir(),'directory-inventory')
    def link(d):
        p=d/'public/operation-comparison.md';p.unlink();p.symlink_to('research-report.md')
    trial('symlink',link,'symlink')
    def hardlink(d):
        p=d/'public/operation-comparison.md';p.unlink();os.link(d/'public/research-report.md',p)
    trial('hardlink',hardlink,'hardlink')
    trial('fifo',lambda d:os.mkfifo(d/'unexpected-fifo'),'object-type')
    def swap(d):
        p=d/'private/context';shutil.rmtree(p);p.write_text('directory replaced')
    trial('directory-to-file',swap,'directory-inventory')
    trial('permission-change',lambda d:(d/'public/status.json').chmod(0o600),'file-integrity:public/status.json')
    # Use explicit revision replacement, independent of URL component indexing.
    def canonical(d):mutate_json(d/'private/upstream/receipts.json',lambda x:x[0].update(url=x[0]['url'].replace('fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','main')))
    trial('reanchored-source-url',canonical,'canonical-raw-url',reanchor=True)
    trial('reanchored-status',lambda d:mutate_json(d/'public/status.json',lambda x:x.update(target_frozen=True)), 'original-status',reanchor=True)
    trial('reanchored-truncated-tree',lambda d:mutate_json(d/'private/context/selected-tree.json',lambda x:x.update(complete_truncated=True)), 'complete-tree-identity',reanchor=True)
    trial('reanchored-primary-version',lambda d:mutate_json(d/'private/primary/receipts.json',lambda x:next(r for r in x if r['id']=='haddad').update(requested_url='https://arxiv.org/pdf/1904.10427v5')), 'primary-identity',reanchor=True)
    trial('reanchored-primary-digest',lambda d:mutate_json(d/'private/primary/receipts.json',lambda x:next(r for r in x if r['id']=='haddad').update(sha256='0'*64)), 'primary-digest',reanchor=True)
    if inventory(source)!=original or digest(source/'manifest.json')!=anchor:raise RuntimeError('sealed-source-mutated')
    print(json.dumps({'controls':'all passed','base_final_anchor':anchor,'sealed_source_unchanged':True,
                      'cases':cases,'mathematical_gate':None,'contribution_gate':None},indent=2))

if __name__=='__main__':main()
