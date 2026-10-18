#!/usr/bin/env python3
"""MIT. Disposable copied controls; original sealed files are never changed."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def main():
    root=Path(__file__).absolute().parent
    expected=hashlib.sha256((root/'manifest.json').read_bytes()).hexdigest()
    snapshot=[p for p in root.rglob('*') if p.is_file()]
    reports=[]
    with tempfile.TemporaryDirectory(prefix='_control_scratch_',dir=root) as tmp:
        tmp=Path(tmp)
        def copy(name):
            dst=tmp/name;dst.mkdir()
            for p in snapshot:
                q=dst/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
            return dst
        def run(name,mutate,accept=False):
            dst=copy(name);entry=mutate(dst) or dst
            r=subprocess.run([sys.executable,str(entry/'verify.py'),expected],capture_output=True,text=True,timeout=20)
            ok=(r.returncode==0)==accept
            reports.append({'case':name,'passed':ok,'expected_accept':accept,'returncode':r.returncode})
            if not ok:raise RuntimeError(name+': '+r.stdout+r.stderr)
        run('unchanged',lambda p:None,True)
        def altered(p): (p/'checkpoint.md').write_text('altered')
        run('altered_payload',altered)
        run('missing_payload',lambda p:(p/'checkpoint.md').unlink())
        run('extra_file',lambda p:(p/'unexpected').touch())
        run('empty_directory',lambda p:(p/'unexpected').mkdir())
        def hard(p):
            q=p/'checkpoint.md';q.unlink();os.link(root/'checkpoint.md',q)
        run('hardlink',hard)
        run('fifo',lambda p:os.mkfifo(p/'pipe'))
        def nested(p):
            q=p/'extra';q.mkdir();(q/'manifest.json').write_text('{}')
        run('nested_manifest',nested)
        def rootlink(p):
            q=p.with_name(p.name+'_link');q.symlink_to(p,target_is_directory=True);return q
        run('root_symlink',rootlink)
        def ancestor(p):
            q=p.with_name(p.name+'_ancestor');q.symlink_to(tmp,target_is_directory=True);return q/p.name
        run('ancestor_symlink',ancestor)
        def reseal(p):
            altered(p);mp=p/'manifest.json';m=json.loads(mp.read_text());b=(p/'checkpoint.md').read_bytes()
            m['files']['checkpoint.md']={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};mp.write_text(json.dumps(m,sort_keys=True))
        run('self_reseal',reseal)
    print(json.dumps({'status':'PASS','snapshot_manifest_sha256':expected,'cases':reports,
      'limit':'Copied controls test the pre-report snapshot; final report inclusion changes the final manifest.'},indent=2))

if __name__=='__main__':main()
