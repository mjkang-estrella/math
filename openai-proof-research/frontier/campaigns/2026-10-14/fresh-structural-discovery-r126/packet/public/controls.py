#!/usr/bin/env python3
"""Copied-input integrity controls; never a mathematical test. MIT."""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib,shutil,subprocess,stat,argparse
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def fingerprint(root):
    out=[]
    for b,ds,fs in os.walk(root,followlinks=False):
        for p in [Path(b),*[Path(b)/n for n in ds+fs]]:
            s=p.lstat();v=[str(p.relative_to(root)),s.st_mode,s.st_nlink]
            if stat.S_ISREG(s.st_mode):v.append(sha(p.read_bytes()))
            elif stat.S_ISLNK(s.st_mode):v.append(os.readlink(p))
            out.append(v)
    return sha(json.dumps(sorted(out),separators=(',',':')).encode())
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--tree',required=True);ap.add_argument('--final-sha256',required=True);a=ap.parse_args()
    r=Path(a.root).absolute();tree=Path(a.tree).absolute();original=r/'packet';final=r/'FINAL.json'
    assert sha(final.read_bytes())==a.final_sha256
    before=fingerprint(original);before_final=final.read_bytes();before_tree=sha(tree.read_bytes())
    work=r/'control-work';work.mkdir(exist_ok=False);results=[]
    cases=['baseline','wrong-anchor','missing-anchor','changed-payload','missing-payload','extra-file','extra-dir','symlink-file','symlink-root','symlink-ancestor','hardlink','duplicate-manifest-key','traversal-record','canonical-record-reanchored','report-binding-reanchored','audit-write','audit-process']
    for name in cases:
        case=work/name;case.mkdir();p=case/'packet';shutil.copytree(original,p);f=case/'FINAL.json';shutil.copy2(final,f);h=a.final_sha256;argp=p
        if name=='wrong-anchor':h='0'*64
        elif name=='changed-payload':(p/'public/report.md').write_bytes(b'changed')
        elif name=='missing-payload':(p/'public/report.md').unlink()
        elif name=='extra-file':(p/'unexpected').write_bytes(b'x')
        elif name=='extra-dir':(p/'unexpected').mkdir()
        elif name=='symlink-file':
            q=p/'public/report.md';q.unlink();q.symlink_to('RIGHTS.md')
        elif name=='symlink-root':
            q=case/'linked';q.symlink_to('packet');argp=q
        elif name=='symlink-ancestor':
            q=work/'linked-ancestor';q.symlink_to(name);argp=q/'packet'
        elif name=='hardlink':
            q=p/'public/report.md';q.unlink();os.link(p/'public/RIGHTS.md',q)
        elif name in ['duplicate-manifest-key','traversal-record','canonical-record-reanchored','report-binding-reanchored']:
            m=json.loads((p/'MANIFEST.json').read_text())
            if name=='traversal-record':m['files']['../escape']={'bytes':0,'sha256':sha(b''),'mode':420}
            elif name=='canonical-record-reanchored':
                q=p/'private/canonical.json';z=json.loads(q.read_text());z[0]['canonical']['url']='https://invalid.example/canonical';q.write_text(json.dumps(z,indent=2)+'\n');m['files']['private/canonical.json'].update(bytes=q.stat().st_size,sha256=sha(q.read_bytes()))
            elif name=='report-binding-reanchored':
                q=p/'public/report.md';q.write_text('changed report\n');m['files']['public/report.md'].update(bytes=q.stat().st_size,sha256=sha(q.read_bytes()))
            b=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode()
            if name=='duplicate-manifest-key':b=b.replace(b'{',b'{"schema":"duplicate",',1)
            (p/'MANIFEST.json').write_bytes(b);z=json.loads(f.read_text());z['manifest_sha256']=sha(b);f.write_text(json.dumps(z,indent=2,sort_keys=True)+'\n');h=sha(f.read_bytes())
        cmd=[sys.executable,'-B',str(p/'public/verify.py'),'--packet',str(argp),'--final',str(f),'--tree',str(tree)]
        if name!='missing-anchor':cmd+=['--final-sha256',h]
        if name=='audit-write':cmd+=['--audit-probe','write']
        if name=='audit-process':cmd+=['--audit-probe','process']
        prior=fingerprint(case);c=subprocess.run(cmd,capture_output=True,text=True);after=fingerprint(case)
        ok=(c.returncode==0) if name=='baseline' else (c.returncode!=0)
        assert ok and prior==after,(name,c.stdout,c.stderr)
        results.append({'case':name,'expected':'accept' if name=='baseline' else 'reject','exit':c.returncode,'stdout':c.stdout,'stderr':c.stderr,'copy_unchanged':prior==after})
        if name=='symlink-ancestor':(work/'linked-ancestor').unlink()
        shutil.rmtree(case)
    work.rmdir();assert fingerprint(original)==before and final.read_bytes()==before_final and sha(tree.read_bytes())==before_tree
    out={'status':'EXPECTED_ARTIFACT_RESULTS','cases':results,'original_packet_before':before,'original_packet_after':fingerprint(original),'original_FINAL_unchanged':True,'external_tree_unchanged':True,'mathematical_gate':False}
    (r/'controls.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'cases':len(results),'all_expected':True,'originals_unchanged':True,'mathematical_gate':False}))
if __name__=='__main__':main()
