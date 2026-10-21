#!/usr/bin/env python3
"""Read-only exact-membership verification. Supply detached anchors from the handoff.
This checks artifacts only, never mathematics, correctness, contribution, or acceptance.
"""
import argparse,hashlib,json,os
from pathlib import Path,PurePosixPath

ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.sha256'}
def digest(data): return hashlib.sha256(data).hexdigest()
def safe_name(s):
    assert isinstance(s,str) and s and '\\' not in s
    p=PurePosixPath(s)
    assert not p.is_absolute() and str(p)==s and all(x not in ('','.','..') for x in s.split('/'))
    return s

def inventory(root):
    files=set(); dirs=set()
    def visit(d):
        for ent in os.scandir(d):
            p=Path(ent.path); rel=p.relative_to(root).as_posix()
            assert not ent.is_symlink(),('symlink',rel)
            if ent.is_dir(follow_symlinks=False): dirs.add(rel);visit(p)
            elif ent.is_file(follow_symlinks=False):files.add(rel)
            else:raise AssertionError(('non-regular entry',rel))
    assert root.is_dir() and not root.is_symlink();visit(root)
    return files,dirs

def check_payload(root,entries,expected_dirs,envelopes=()):
    names=[safe_name(e['path']) for e in entries]
    assert len(names)==len(set(names)),'duplicate manifest paths'
    assert not set(names)&set(envelopes),'envelope included in payload'
    ds={safe_name(d) for d in expected_dirs}
    observed,dirs=inventory(root)
    assert observed==set(names)|set(envelopes),('file membership mismatch',sorted(observed^(set(names)|set(envelopes))))
    assert dirs==ds,('directory membership mismatch',sorted(dirs^ds))
    for e in entries:
        p=root/e['path']; b=p.read_bytes()
        assert len(b)==e['bytes'],('size',e['path'])
        assert digest(b)==e['sha256'],('hash',e['path'])
        assert oct(p.stat().st_mode&0o777)==e['mode'],('mode',e['path'])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    for name in ['final','manifest','report']:ap.add_argument('--'+name+'-sha256',required=True)
    args=ap.parse_args();root=args.root.absolute()
    expected={name.upper()+'.md' if name!='manifest' else 'MANIFEST.json':getattr(args,name+'_sha256') for name in ['final','manifest','report']}
    # FINAL and REPORT names have uppercase stems, lower-case suffixes.
    for name,h in expected.items():
        assert len(h)==64 and all(c in '0123456789abcdef' for c in h)
        p=root/name;assert not p.is_symlink();assert digest(p.read_bytes())==h,('detached anchor',name)
    canonical=''.join(expected[name]+'  '+name+'\n' for name in ['FINAL.md','MANIFEST.json','REPORT.md'])
    assert (root/'ANCHORS.sha256').read_text()==canonical,'detached anchor file'
    manifest=json.loads((root/'MANIFEST.json').read_text())
    assert set(manifest['envelopes'])==ENVELOPES
    check_payload(root,manifest['files'],manifest['directories'],ENVELOPES)
    assert digest((root/'FROZEN.md').read_bytes())=='cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77'
    assert digest((root/'private/original-author-proof.md').read_bytes())=='6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446'
    print(json.dumps({'artifact_verification':'matched','payload_files':len(manifest['files']),'exact_directories':len(manifest['directories']),'mathematical_gate':False}))
if __name__=='__main__':main()
