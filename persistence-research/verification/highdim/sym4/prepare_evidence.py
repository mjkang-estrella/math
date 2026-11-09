"""Finalize metadata and preserve the exact driver used by the first two runs."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def main():
    p = HERE/'prime_ranking.json'
    rows = json.loads(p.read_text())
    # ord_1000(3)=100 and ord_1000(7)=20, including the 2-adic factors.
    for b,expected in ((3,100),(7,20)):
        x,n = b%1000,1
        while x!=1:
            x=x*b%1000
            n+=1
        assert n==expected
    for r in rows:
        r['tail3_periods']=[100,20]
        r['tail3_step_index']=(r['p']-1)//math.lcm(r['order3']//math.gcd(r['order3'],100),
                                                r['order7']//math.gcd(r['order7'],20))
    p.write_text(json.dumps(rows,indent=1)+'\n')
    p = HERE/'assignment.json'
    assignment = json.loads(p.read_text())
    source = HERE.parent/'sym2/summary.json'
    assert set(assignment['configurations'])==set(json.loads(source.read_text())['open'])
    assignment['source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    p.write_text(json.dumps(assignment,indent=1)+'\n')
    code = (HERE/'continue_sym2.py').read_text()
    start = code.index('\ndef reconcile():\n')
    end = code.index('\ndef slices(',start)
    old = code[:start]+code[end:]
    old = old.replace('def legacy_reconcile():','def reconcile():',1)
    new_dispatch = '''    elif a.mode == 'check':
        subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I "$@"','sym4-replay',
                        str(HERE/'replay_dual.py'),'--workers',str(a.workers)],check=True)
    else:
        subprocess.run(['bash','-c','ulimit -v 8000000; python3 -I "$@"','sym4-coverage',
                        str(HERE/'audit_coverage.py')],check=True)'''
    assert new_dispatch in old
    old = old.replace(new_dispatch,"    elif a.mode == 'check': checks(a)\n    else: audit()")
    digest = hashlib.sha256(old.encode()).hexdigest()
    expected = [json.loads((HERE/('input_'+s+'.json')).read_text())['code_hashes']['continue_sym2.py']
                for s in ('tailrank235','floor235')]
    assert all(digest==v for v in expected),(digest,expected)
    snap = HERE/'source_snapshots'
    snap.mkdir(exist_ok=True)
    (snap/'continue_sym2_initial.py').write_text(old)
    print(json.dumps({'assignment':len(assignment['configurations']),'initial_driver_sha256':digest,
                      'snapshot_result':'PASS','tail3_periods':[100,20]}))


if __name__=='__main__':
    main()
