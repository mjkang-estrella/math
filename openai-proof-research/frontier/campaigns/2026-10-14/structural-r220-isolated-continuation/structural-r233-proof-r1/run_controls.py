#!/usr/bin/env python3
"""Tiny own-root copied artifact controls; never touches author files."""
from pathlib import Path
import hashlib,importlib.util,json
root=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('review_verifier',root/'verify_packet.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
d=root/'controls';d.mkdir(exist_ok=False);copydir=d/'copy';copydir.mkdir()
original=d/'original.txt';original.write_bytes(b'copied integrity control\n');original.chmod(0o444)
f=copydir/'copy.txt';f.write_bytes(original.read_bytes());f.chmod(0o444)
e={'path':'copy.txt','bytes':f.stat().st_size,'mode':'0444','sha256':v.sha(f)};before=(v.sha(original),original.stat().st_mode)
results=[]
def check(name,action,expect_error):
    try:action()
    except ValueError:
        if not expect_error:raise
        results.append({'control':name,'result':'rejected as expected'})
    else:
        if expect_error:raise AssertionError(name+' unexpectedly accepted')
        results.append({'control':name,'result':'accepted as expected'})
check('unchanged copied payload',lambda:v.verify_payload(copydir,[e],['copy.txt']),False)
check('exact copied surface',lambda:v.verify_surface(copydir,['copy.txt']),False)
f.chmod(0o644);f.write_bytes(original.read_bytes()+b'x');f.chmod(0o444)
check('one-byte changed copy',lambda:v.verify_payload(copydir,[e],['copy.txt']),True)
f.chmod(0o644);f.write_bytes(original.read_bytes())
check('changed copy mode',lambda:v.verify_payload(copydir,[e],['copy.txt']),True);f.chmod(0o444)
check('selection omission',lambda:v.verify_payload(copydir,[e],[]),True)
extra=copydir/'extra.txt';extra.write_bytes(b'x');extra.chmod(0o444)
check('undeclared surface file',lambda:v.verify_surface(copydir,['copy.txt']),True);extra.unlink()
assert before==(v.sha(original),original.stat().st_mode)
v.verify_payload(copydir,[e],['copy.txt']);v.verify_surface(copydir,['copy.txt'])
(root/'artifact-controls.json').write_text(json.dumps({'original_bytes':original.stat().st_size,'original_sha256':v.sha(original),'original_unchanged':True,'restored_copy_valid':True,'tests':results,'mathematical_gate':False},indent=2)+'\n')
print(json.dumps({'copied_control_bytes':original.stat().st_size,'tests':len(results),'all_expected_results':True,'original_unchanged':True,'mathematical_gate':False}))
