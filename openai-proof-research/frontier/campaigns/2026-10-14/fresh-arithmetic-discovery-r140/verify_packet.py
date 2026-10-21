#!/usr/bin/env python3
"""Read-only artifact verification; external anchors mandatory; no mathematical gate."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',required=True,type=Path)
    for name in ['final','manifest','report']:
        parser.add_argument('--'+name+'-sha256',required=True)
    args=parser.parse_args();root=args.root.resolve()
    for filename,key in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:
        path=root/filename
        assert not path.is_symlink(),f'symlink anchor: {filename}'
        assert digest(path)==getattr(args,key+'_sha256'),f'anchor mismatch: {filename}'
    manifest=json.loads((root/'MANIFEST.json').read_text())
    assert manifest['schema']=='r140-exact-selection-v1'
    seen=set()
    for e in manifest['entries']:
        rel=PurePosixPath(e['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        assert str(rel) not in seen,'duplicate manifest path'
        seen.add(str(rel))
        path=root.joinpath(*rel.parts)
        assert path.resolve().is_relative_to(root),'escaped root'
        assert all(not root.joinpath(*rel.parts[:i]).is_symlink() for i in range(1,len(rel.parts)+1)),'symlink payload'
        assert path.is_file() and path.stat().st_size==e['bytes'],f'length mismatch: {rel}'
        assert digest(path)==e['sha256'],f'payload mismatch: {rel}'
    print(f'Artifact verification passed: {len(seen)} exact selected payload files and three external anchors. No mathematical grade.')

if __name__=='__main__':main()
