#!/usr/bin/env python3
"""Reproduce disposable verifier controls entirely inside the owned directory."""
import hashlib
import json
from pathlib import Path
import tempfile

base=Path(__file__).resolve().parents[1]
namespace={'__name__':'verifier_control_import','__file__':str(base/'public/verify.py')}
exec(compile((base/'public/verify.py').read_text(),str(base/'public/verify.py'),'exec'),namespace)
validate=namespace['inventory']; safe_path=namespace['safe_path']; verify=namespace['verify']

def record(path,data): return {'path':path,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

def case(kind):
    with tempfile.TemporaryDirectory(prefix='_integrity-control-',dir=base) as tmp:
        p=Path(tmp); (p/'sub').mkdir(); (p/'a').write_bytes(b'a'); (p/'sub/b').write_bytes(b'b')
        records=[record('a',b'a'),record('sub/b',b'b')]; dirs=['sub']
        if kind=='changed': (p/'a').write_bytes(b'c')
        if kind=='missing': (p/'a').unlink()
        if kind=='extra_file': (p/'extra').write_bytes(b'x')
        if kind=='extra_directory': (p/'empty').mkdir()
        if kind=='symlink': (p/'a').unlink(); (p/'a').symlink_to('sub/b')
        if kind=='duplicate': records.append(records[0])
        before={str(f.relative_to(p)):f.read_bytes() for f in p.rglob('*') if f.is_file() and not f.is_symlink()}
        rejected=False
        try: validate(p,records,dirs)
        except ValueError: rejected=True
        after={str(f.relative_to(p)):f.read_bytes() for f in p.rglob('*') if f.is_file() and not f.is_symlink()}
        assert before==after
        assert rejected==(kind!='positive'),kind
        return 'accepted_read_only' if not rejected else 'rejected_read_only'

results={kind:case(kind) for kind in ['positive','changed','missing','extra_file','extra_directory','symlink','duplicate']}
with tempfile.TemporaryDirectory(prefix='_integrity-control-',dir=base) as tmp:
    p=Path(tmp); (p/'MANIFEST.json').write_bytes(b'{}')
    for name,anchor in [('wrong_detached_anchor','0'*64),('malformed_detached_anchor','bad')]:
        try: verify(p,p,anchor)
        except ValueError: results[name]='rejected'
        else: raise AssertionError(name)
    for name in ['../escape','/absolute','sub/../a','']:
        try: safe_path(p,name)
        except ValueError: pass
        else: raise AssertionError(name)
results['unsafe_paths']='four rejected'
print(json.dumps({'kind':'integrity behavior only; no mathematical or independent gate','cases':results},indent=2))
