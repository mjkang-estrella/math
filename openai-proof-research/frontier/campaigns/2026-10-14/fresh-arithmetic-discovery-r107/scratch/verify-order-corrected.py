#!/usr/bin/env python3
"""Read-only exact payload/three detached anchor verifier; no math verdict."""
import argparse,hashlib,json,os,re
from pathlib import Path

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
    result=[]
    for base in ['notes','controls','private']:
        assert (root/base).is_dir() and not (root/base).is_symlink(), base
        for here,dirs,files in os.walk(root/base,followlinks=False):
            for name in dirs+files:
                assert not Path(here,name).is_symlink(), 'symlink'
            for name in files: result.append(str(Path(here,name).relative_to(root)))
    result += ['READING.md','RIGHTS.md']
    return sorted(result)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    for x in ['manifest','final','report']:ap.add_argument('--'+x+'-sha',required=True)
    a=ap.parse_args(); root=a.root.resolve()
    for name,expected in [('MANIFEST.json',a.manifest_sha),('FINAL.md',a.final_sha),('REPORT.md',a.report_sha)]:
        assert re.fullmatch('[0-9a-f]{64}',expected), 'invalid detached anchor'
        assert not (root/name).is_symlink(), 'symlink'
        assert digest(root/name)==expected, 'detached mismatch: '+name
    allowed={'notes','controls','private','scratch','READING.md','RIGHTS.md','MANIFEST.json','FINAL.md','REPORT.md','SHA256SUMS','artifact-controls.json'}
    assert set(x.name for x in root.iterdir())<=allowed, 'unexpected outer entry'
    manifest=json.loads((root/'MANIFEST.json').read_text())
    assert manifest['scope']=={'directories':['notes','controls','private'],'root_files':['READING.md','RIGHTS.md']}, 'scope'
    rows=manifest['files']; names=[x['path'] for x in rows]
    assert len(names)==len(set(names)), 'duplicates'
    assert sorted(names)==inventory(root), 'exact inventory mismatch'
    for x in rows:
        path=Path(x['path']); assert not path.is_absolute() and '..' not in path.parts, 'unsafe path'
        p=root/path; assert not p.is_symlink() and p.is_file(), 'not regular file'
        assert p.stat().st_size==x['size'] and digest(p)==x['sha256'], 'payload mismatch: '+x['path']
    print(json.dumps({'artifact_integrity':'verified','payload_files':len(rows),'mathematical_verdict':None}))
if __name__=='__main__':main()
