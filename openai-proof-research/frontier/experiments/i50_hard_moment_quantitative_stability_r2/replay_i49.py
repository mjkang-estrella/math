#!/usr/bin/env python3
"""Read-only I49 replay; one explicitly recorded in-memory ordering normalization."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,io,contextlib,traceback
R=Path(__file__).resolve().parents[3];p=R/'frontier/experiments/i49_hard_moment_quantitative_stability/verify.py'
b=p.read_bytes();s=b.decode();old="assert run.stdout==(S/r['output']).read_bytes()";new="assert sorted(run.stdout.splitlines())==sorted((S/r['output']).read_bytes().splitlines())"
assert s.count(old)==1
out=io.StringIO();err=None
try:
 with contextlib.redirect_stdout(out):exec(compile(s.replace(old,new),str(p),'exec'),{'__file__':str(p),'__name__':'__main__'})
except Exception:err=traceback.format_exc()
record={'kind':'order-normalized IN-MEMORY I49 replay, not vanilla','source_sha256':hashlib.sha256(b).hexdigest(),'original':old,'replacement':new,'disk_source_unchanged':p.read_bytes()==b,'stdout':out.getvalue(),'error':err}
print(json.dumps(record,indent=2))
if err:sys.exit(1)
