"""Bounded negatives exercise the actual verifier validation functions without disk mutation."""
import verify,json,pathlib
P=pathlib.Path(__file__).parent
b=b'abc';e=dict(path='synthetic',size=3,sha256=verify.sha(b));out=[]
for name,fn in [('same_size_hash',lambda:verify.check_bytes(b'abd',e)),('size',lambda:verify.check_bytes(b'abcd',e)),('extra_file',lambda:verify.check_names(['a','extra'],['a']))]:
 try:fn()
 except ValueError as ex:out.append(dict(test=name,rejected=True,exit_semantics='verify.main catches exception and exits1',detail=str(ex)))
 else:raise AssertionError('negative accepted: '+name)
print(json.dumps(out,indent=2))
