#!/usr/bin/env python3
"""Copied artifact mutations only; no mathematical tests."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path

def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root,exclude):
    files={};dirs=[]
    for p in sorted(root.rglob('*')):
        if p==exclude or exclude in p.parents:continue
        s=p.relative_to(root).as_posix()
        if p.is_symlink():files[s]={'symlink':os.readlink(p)}
        elif p.is_dir():dirs.append(s)
        else:files[s]={'sha256':h(p),'bytes':p.stat().st_size}
    return {'files':files,'directories':dirs}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('root',type=Path);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--tree',required=True,type=Path);a=ap.parse_args()
    root=a.root.resolve();tree=a.tree.resolve();out=root/'work/controls'
    if out.exists():raise ValueError('controls destination already exists; preserve receipt')
    out.mkdir(parents=True);before=snapshot(root,out);rows=[]
    source=json.loads((root/'packet/public/source-register.json').read_text())[0]['local']
    primary=json.loads((root/'packet/public/primary-register.json').read_text())[0]['pdf']
    names=['positive','missing-final-argument','wrong-final-anchor','wrong-report-anchor','report-change','manifest-change','final-change','extra-file','extra-directory','missing-file','source-change','primary-change','symlink','hardlink','forged-chain','verifier-change','wrong-tree','audit-write','audit-subprocess']
    for name in names:
        case=out/name;case.mkdir();shutil.copytree(root/'packet',case/'packet')
        for f in ['MANIFEST.json','FINAL.json']:shutil.copyfile(root/f,case/f)
        original=snapshot(case,case/'nonexistent-exclusion')
        fhash=a.finalhash;rhash=a.reporthash;ctree=tree
        report=case/'packet/public/report.md'
        if name=='wrong-final-anchor':fhash='0'*64
        elif name=='wrong-report-anchor':rhash='0'*64
        elif name=='report-change':report.write_bytes(report.read_bytes()+b'\nmutation\n')
        elif name=='manifest-change':(case/'MANIFEST.json').write_bytes((case/'MANIFEST.json').read_bytes()+b' ')
        elif name=='final-change':(case/'FINAL.json').write_bytes((case/'FINAL.json').read_bytes()+b' ')
        elif name=='extra-file':(case/'packet/extra').write_text('x')
        elif name=='extra-directory':(case/'packet/empty-extra').mkdir()
        elif name=='missing-file':report.unlink()
        elif name=='source-change':
            p=case/'packet'/source;p.write_bytes(p.read_bytes()+b'\n% mutation\n')
        elif name=='primary-change':
            p=case/'packet'/primary;p.write_bytes(p.read_bytes()+b'\nmutation\n')
        elif name=='symlink':
            report.unlink();report.symlink_to(root/'packet/public/report.md')
        elif name=='hardlink':
            p=case/'report-backing';shutil.copyfile(report,p);report.unlink();os.link(p,report)
        elif name=='forged-chain':
            report.write_bytes(report.read_bytes()+b'\nforged\n');m=json.loads((case/'MANIFEST.json').read_text());m['files']['public/report.md']={'sha256':h(report),'bytes':report.stat().st_size};(case/'MANIFEST.json').write_text(json.dumps(m)+'\n');f=json.loads((case/'FINAL.json').read_text());f['manifest_sha256']=h(case/'MANIFEST.json');f['report_sha256']=h(report);(case/'FINAL.json').write_text(json.dumps(f)+'\n')
        elif name=='verifier-change':
            p=case/'packet/public/verify.py';p.write_bytes(p.read_bytes()+b'\n# mutation\n')
        elif name=='wrong-tree':
            ctree=case/'altered-tree.json';ctree.write_bytes(tree.read_bytes()+b' ')
        cmd=[sys.executable,'-B',str(case/'packet/public/verify.py'),str(case),'--finalhash',fhash,'--reporthash',rhash,'--tree',str(ctree)]
        if name=='missing-final-argument':del cmd[4:6]
        if name.startswith('audit-'):
            op="open(str(p/'denied-write'),'w')" if name=='audit-write' else "__import__('subprocess').run(['true'])"
            probe="import runpy\nfrom pathlib import Path\np=Path("+repr(str(case))+ ")\nrunpy.run_path(str(p/'packet/public/verify.py'),run_name='audit_probe')\ntry:\n "+op+"\nexcept PermissionError:\n print('DENIED_AS_EXPECTED')\nelse:\n raise SystemExit('audit guard failed')\n"
            cmd=[sys.executable,'-B','-c',probe]
        tested_before=snapshot(case,case/'nonexistent-exclusion')
        r=subprocess.run(cmd,text=True,capture_output=True,timeout=60)
        tested_after=snapshot(case,case/'nonexistent-exclusion')
        expect_success=name in ['positive','audit-write','audit-subprocess']
        ok=(r.returncode==0)==expect_success and tested_before==tested_after
        if name=='positive':ok=ok and original==tested_after
        rows.append({'control':name,'expected':'success' if expect_success else 'rejection','exit':r.returncode,'as_expected':ok,'copied_input_unchanged_by_verifier':tested_before==tested_after,'stdout':r.stdout,'stderr':r.stderr})
        shutil.rmtree(case)
    after=snapshot(root,out)
    result={'kind':'artifact_integrity_only','mathematical_gate':False,'final_sha256':a.finalhash,'report_sha256':a.reporthash,'manifest_sha256':h(root/'MANIFEST.json'),'tree_sha256':h(tree),'original_root_unchanged_excluding_only_control_output_subtree':before==after,'original_snapshot_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest(),'control_count':len(rows),'all_as_expected':all(x['as_expected'] for x in rows),'controls':rows}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'original-snapshot.json').write_text(json.dumps(before,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='controls'},sort_keys=True))
    if not result['all_as_expected'] or not before==after:raise SystemExit(1)
if __name__=='__main__':main()
