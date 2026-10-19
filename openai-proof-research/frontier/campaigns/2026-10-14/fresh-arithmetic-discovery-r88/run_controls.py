#!/usr/bin/env python3
"""Original r88 copied integrity controls. No mathematical tests."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True

def sha(b):return hashlib.sha256(b).hexdigest()
def snap(root,exclude=None):
    out={}
    def visit(p):
        if exclude is not None and p==exclude:return
        st=p.lstat();rel=str(p.relative_to(root));v={'mode':stat.S_IMODE(st.st_mode),'type':stat.S_IFMT(st.st_mode)}
        if stat.S_ISREG(st.st_mode):v.update(sha256=sha(p.read_bytes()),size=st.st_size,nlink=st.st_nlink)
        elif stat.S_ISLNK(st.st_mode):v['target']=os.readlink(p)
        out[rel]=v
        if stat.S_ISDIR(st.st_mode):
            for x in sorted(p.iterdir()):visit(x)
    visit(root);return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--out',required=True);a=ap.parse_args()
    root=Path(a.root).resolve();out=(root/a.out).resolve()
    if not out.is_relative_to(root) or out==root or out.exists():raise ValueError('output must be NEW inside selected root')
    if sha((root/'FINAL.json').read_bytes())!=a.finalhash or sha((root/'REPORT.md').read_bytes())!=a.reporthash:raise ValueError('detached anchors mismatch')
    final=json.loads((root/'FINAL.json').read_text())
    if sha(Path(__file__).read_bytes())!=final['anchors']['run_controls.py']['sha256']:raise ValueError('runner anchor mismatch')
    original=snap(root);out.mkdir();rows=[]
    cases=['baseline','missing-finalhash','wrong-finalhash','wrong-reporthash','report-mutation','manifest-mutation','verifier-mutation','runner-mutation','payload-mutation','missing-payload','extra-payload','extra-directory','symlink','fifo','directory-mode','file-mode','tree-mutation','coherent-reseal-old-anchor','deny-write','deny-process']
    for case in cases:
        c=out/'disposable';c.mkdir()
        shutil.copytree(root/'packet',c/'packet')
        for n in ['FINAL.json','REPORT.md','MANIFEST.json','verify.py','run_controls.py']:shutil.copy2(root/n,c/n)
        target=c/'packet/public/report.md';args=[sys.executable,'-B',str(c/'verify.py'),'--root',str(c),'--finalhash',a.finalhash,'--reporthash',a.reporthash]
        if case=='missing-finalhash':args=args[:-4]+args[-2:]
        elif case=='wrong-finalhash':args[args.index('--finalhash')+1]='0'*64
        elif case=='wrong-reporthash':args[args.index('--reporthash')+1]='0'*64
        elif case=='report-mutation':(c/'REPORT.md').write_text('changed')
        elif case=='manifest-mutation':(c/'MANIFEST.json').write_text('{}')
        elif case=='verifier-mutation':
            with (c/'verify.py').open('a') as f:f.write('\n# mutated\n')
        elif case=='runner-mutation':(c/'run_controls.py').write_text('changed')
        elif case=='payload-mutation':target.write_text('changed')
        elif case=='missing-payload':target.unlink()
        elif case=='extra-payload':(c/'packet/EXTRA').write_text('extra')
        elif case=='extra-directory':(c/'packet/EXTRA').mkdir()
        elif case=='symlink':target.unlink();target.symlink_to('../private/context/AGENTS.md')
        elif case=='fifo':os.mkfifo(c/'packet/FIFO')
        elif case=='directory-mode':(c/'packet/public').chmod(0o700)
        elif case=='file-mode':target.chmod(0o600)
        elif case=='tree-mutation':(c/'packet/private/context/preprints-tree.json').write_text('{"tree":[],"truncated":false}')
        elif case=='coherent-reseal-old-anchor':
            target.write_text('coherently changed');m=json.loads((c/'MANIFEST.json').read_text());v=m['files']['public/report.md'];v['sha256']=sha(target.read_bytes());v['size']=target.stat().st_size;(c/'MANIFEST.json').write_text(json.dumps(m));f=json.loads((c/'FINAL.json').read_text());f['anchors']['MANIFEST.json']['sha256']=sha((c/'MANIFEST.json').read_bytes());f['anchors']['MANIFEST.json']['size']=(c/'MANIFEST.json').stat().st_size;(c/'FINAL.json').write_text(json.dumps(f))
        elif case=='deny-write':args.append('--probe-write')
        elif case=='deny-process':args.append('--probe-process')
        before=snap(c);res=subprocess.run(args,capture_output=True,text=True,timeout=40);after=snap(c)
        expected=(res.returncode==0) if case=='baseline' else (res.returncode!=0)
        if case=='deny-write':expected=expected and 'DENIED_WRITE' in res.stderr
        if case=='deny-process':expected=expected and 'DENIED_PROCESS_OR_NETWORK' in res.stderr
        row=dict(case=case,returncode=res.returncode,expected_outcome=expected,copied_inputs_unchanged=(before==after),stdout=res.stdout,stderr=res.stderr);rows.append(row)
        if not expected or before!=after:raise RuntimeError(json.dumps(row))
        shutil.rmtree(c)
    original_after=snap(root,exclude=out)
    if original_after!=original:raise RuntimeError('preexisting original root changed')
    receipt=dict(status='INTEGRITY_CONTROLS_ONLY',final_sha256=a.finalhash,report_sha256=a.reporthash,cases=rows,original_preexisting_tree_unchanged=True,original_snapshot_sha256=sha(json.dumps(original,sort_keys=True).encode()))
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(cases=len(rows),expected=True,original_preexisting_tree_unchanged=True,receipt=str(out/'receipt.json'))))
if __name__=='__main__':main()
