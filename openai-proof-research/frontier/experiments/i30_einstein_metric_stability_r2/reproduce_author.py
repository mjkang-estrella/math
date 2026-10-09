#!/usr/bin/env python3
"""Run exact author code with its two output writes redirected into review scope.

The original scripts are never modified or imported (no pycache). The substitutions
are asserted literal matches and recorded. Mathematical checking is separate.
"""
from pathlib import Path
import contextlib, io, json, sys, hashlib
R=Path(__file__).resolve().parents[3]
E=Path(__file__).resolve().parent
author=R/'frontier/experiments/i30_einstein_metric_stability'
records=[]
for name in ['diagnostics.py','verify.py','seal.py']:
    p=author/name; original=p.read_text(); code=original; replacements=[]
    if name=='diagnostics.py':
        old="OUT=ROOT/'frontier/experiments/i30_einstein_metric_stability/diagnostics.json'"
        new="OUT=ROOT/'frontier/experiments/i30_einstein_metric_stability_r2/author-diagnostics.json'"
        assert code.count(old)==1;code=code.replace(old,new);replacements.append(dict(old=old,new=new))
    if name=='verify.py':
        old="(E/'verification.json').write_text"
        new="(R/'frontier/experiments/i30_einstein_metric_stability_r2/author-verification.json').write_text"
        assert code.count(old)==1;code=code.replace(old,new);replacements.append(dict(old=old,new=new))
    buf=io.StringIO();oldargv=sys.argv;sys.argv=[str(p)]+(['--verify'] if name=='seal.py' else [])
    rc=0
    try:
        with contextlib.redirect_stdout(buf): exec(compile(code,str(p),'exec'),{'__file__':str(p),'__name__':'__main__'})
    except SystemExit as ex: rc=int(ex.code or 0)
    finally:sys.argv=oldargv
    output=buf.getvalue(); (E/('author-'+name+'.stdout.txt')).write_text(output)
    records.append(dict(script=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_redirects=replacements,returncode=rc,result=json.loads(output)))
    assert rc==0
result=dict(status='PASS',policy='Read-only originals; only output paths redirected. No original reproduction artifacts overwritten.',commands=records)
(E/'author-reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=[r['result'] for r in records]),indent=2))
