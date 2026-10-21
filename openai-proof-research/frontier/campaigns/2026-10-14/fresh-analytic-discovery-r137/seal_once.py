#!/usr/bin/env python3
"""One-time packet seal. Never rewrites an existing final manifest."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
R=Path(__file__).resolve().parent
EX={'MANIFEST.json','FINAL.md','REPORT.md','DETACHED-SHA256.json'}
def sh(b):return hashlib.sha256(b).hexdigest()
def manifest(root):
    files=[]
    for cur,ds,fs in os.walk(root,followlinks=False):
        for n in ds+fs:
            if (Path(cur)/n).is_symlink():raise ValueError('symlink')
        for n in fs:
            p=Path(cur)/n;name=p.relative_to(root).as_posix()
            if name in EX:continue
            b=p.read_bytes();files.append(dict(path=name,size=len(b),sha256=sh(b)))
    return dict(schema='r137-artifact-v1',excluded_envelopes=sorted(EX),files=sorted(files,key=lambda x:x['path']))
if __name__=='__main__':
    if (R/'MANIFEST.json').exists():raise SystemExit('Already sealed; refusing rewrite')
    for name in ['FINAL.md','REPORT.md','artifact-controls.json','current-original-observations.json']:
        if not (R/name).is_file():raise SystemExit('Missing '+name)
    (R/'MANIFEST.json').write_text(json.dumps(manifest(R),indent=2)+'\n')
    anchors={n:sh((R/n).read_bytes()) for n in ['MANIFEST.json','FINAL.md','REPORT.md']}
    (R/'DETACHED-SHA256.json').write_text(json.dumps(anchors,indent=2)+'\n')
    cmd=[sys.executable,str(R/'verify_readonly.py'),'--root',str(R),'--manifest-sha256',anchors['MANIFEST.json'],'--final-sha256',anchors['FINAL.md'],'--report-sha256',anchors['REPORT.md']]
    result=subprocess.run(cmd,capture_output=True,text=True,check=False)
    print(result.stdout.strip());print(json.dumps(anchors,indent=2))
    raise SystemExit(result.returncode)
