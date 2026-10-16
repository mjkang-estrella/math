#!/usr/bin/env python3
"""Read-only exact pencil probe, MIT, Myeongjin Kang.

Authenticate the only local code dependency before loading it. This probe
does not exhaust regular sequences or ideals; it inspects stated finite pencils.
"""
from pathlib import Path
import hashlib
import json
import runpy
from itertools import product

SOURCE_SHA256='fdf2bc99a32416f72babbe5ab87b07015e41ff97444af5ea2c3a0d50ee728b07'
p=Path(__file__).resolve().with_name('tate_checks.py')
assert hashlib.sha256(p.read_bytes()).hexdigest()==SOURCE_SHA256
ns=runpy.run_path(str(p),run_name='authenticated_library')
Q,betti,table,pure=[ns[k] for k in ['Quotient','betti','table','pure']]

def main():
    records=[]; nonregular=[]; counterexamples=[]
    # Each row's two allowed cross terms belong to all the fixed I below.
    cross=[(1,1,0),(1,0,1)]
    ideals=[pure(3,(2,2,2))+[{cross[0]:1}],
            pure(3,(2,2,2))+[{cross[0]:1},{cross[1]:1}],
            pure(3,(2,2,2))+[{cross[0]:1},{cross[1]:1},{(0,1,1):1}]]
    coeffs=list(product((-1,0,1),repeat=3))
    for ii,igs in enumerate(ideals):
        m=Q(3,igs,3)
        lex=ns['lex_ideal'](3,(2,2,2),m.hf())
        lex_b,_=betti(lex,pure(3,(2,2,2)),5)
        for a,b,c in coeffs:
            fs=pure(3,(2,2,2))
            fs[0][cross[0]]=a
            fs[1][cross[0]]=b
            fs[2][cross[0]]=c
            fs=[{x:v for x,v in f.items() if v} for f in fs]
            try:
                r=Q(3,fs,3)
            except AssertionError:
                nonregular.append([ii,a,b,c]);continue
            assert r.hf()==(1,3,3,1)
            # I contains all f, so the quotient M stays fixed exactly.
            for f in fs:
                assert not m.reduce(f,2)
            bt,_=betti(m,fs,5)
            bad=[(p,j,v,lex_b.get((p,j),0)) for (p,j),v in bt.items()
                 if v>lex_b.get((p,j),0)]
            if bad:counterexamples.append([ii,a,b,c,bad])
            records.append({'ideal':ii,'coefficients':[a,b,c],
                            'relative':table(bt,5)})
    distinct={}
    for i in range(3):
        vals={json.dumps(e['relative']) for e in records if e['ideal']==i}
        distinct[str(i)]=[json.loads(x) for x in sorted(vals)]
    serial=json.dumps(records,sort_keys=True,separators=(',',':'))
    print(json.dumps({'status':'FINITE_PENCIL_PROBE_ONLY',
                      'regular_cases':len(records),'excluded_nonregular':nonregular,
                      'homological_degrees':[0,5],
                      'distinct_tables_by_fixed_module':distinct,
                      'counterexamples':counterexamples,
                      'records_sha256':hashlib.sha256(serial.encode()).hexdigest(),
                      'records':records},indent=2,sort_keys=True))

if __name__=='__main__':main()
