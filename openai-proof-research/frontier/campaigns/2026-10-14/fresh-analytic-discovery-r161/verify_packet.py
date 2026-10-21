"""Read-only exact-packet verifier. Detached anchors must come from the handoff.
This checks artifacts only, never mathematical truth or contribution.
"""
import argparse, hashlib, json, os, pathlib, sys
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    result={}
    def visit(d):
        for e in os.scandir(d):
            p=pathlib.Path(e.path); rel=p.relative_to(root).as_posix()
            if e.is_symlink(): raise ValueError('symlink: '+rel)
            if e.is_dir(follow_symlinks=False): visit(p)
            elif e.is_file(follow_symlinks=False):
                if rel not in ENVELOPES:
                    b=p.read_bytes();result[rel]={'bytes':len(b),'sha256':sha(b)}
            else: raise ValueError('nonregular entry: '+rel)
    visit(root)
    return result
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',required=True)
p.add_argument('--final-sha256',required=True)
p.add_argument('--manifest-sha256',required=True)
p.add_argument('--report-sha256',required=True)
a=p.parse_args();root=pathlib.Path(a.root)
try:
    if root.is_symlink(): raise ValueError('root symlink')
    expected={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    for name,h in expected.items():
        if len(h)!=64 or any(c not in '0123456789abcdef' for c in h): raise ValueError('invalid explicit anchor: '+name)
        f=root/name
        if f.is_symlink() or sha(f.read_bytes())!=h: raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_bytes())
    if m['outside_envelopes']!=sorted(ENVELOPES): raise ValueError('envelope definition mismatch')
    files=m['files'];names=[x['path'] for x in files]
    if names!=sorted(set(names)): raise ValueError('duplicate/unsorted membership')
    for name in names:
        q=pathlib.PurePosixPath(name)
        if q.is_absolute() or '..' in q.parts or q.as_posix()!=name or name in ENVELOPES: raise ValueError('unsafe member')
    wanted={x['path']:{'bytes':x['bytes'],'sha256':x['sha256']} for x in files}
    actual=inventory(root)
    if actual!=wanted:
        missing=sorted(set(wanted)-set(actual));extra=sorted(set(actual)-set(wanted))
        changed=sorted(k for k in set(actual)&set(wanted) if actual[k]!=wanted[k])
        raise ValueError(json.dumps({'missing':missing,'extra':extra,'changed':changed}))
    print(json.dumps({'artifact_verification':'MATCH','payload_files':len(actual),'explicit_detached_anchors':True,'read_only':True,'mathematical_gate':False}))
except (ValueError,OSError,KeyError,TypeError) as e:
    print('ARTIFACT MISMATCH: '+str(e),file=sys.stderr);sys.exit(1)
