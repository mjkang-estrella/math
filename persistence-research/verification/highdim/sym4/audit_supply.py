"""Independent trial-division audit of the 32 NEW prime supply entries.

Certificate validation still uses the two original checker CLIs directly.
"""
import sys
sys.dont_write_bytecode = True
import json
import math
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def prime(n):
    if n < 2:
        return False
    if n%2==0:
        return n==2
    q = 3
    while q*q <= n:
        if n%q==0:
            return False
        q += 2
    return True


def factors(n):
    out = []
    q = 2
    while q*q<=n:
        if n%q==0:
            out.append(q)
            while n%q==0:
                n//=q
        q += 1
    if n>1:
        out.append(n)
    return out


def main():
    rows = json.loads((HERE/'prime_search.json').read_text())['new']
    results = []
    for p,d,a,w in rows:
        assert prime(p),p
        ff = factors(p-1)
        actual = []
        for b in (10,3,7):
            o = p-1
            assert pow(b,o,p)==1
            for q in ff:
                while o%q==0 and pow(b,o//q,p)==1:
                    o//=q
            actual.append(o)
        assert actual==[d,a,w],(p,actual,[d,a,w])
        assert 1<=d<=60 and pow(10,d,p)==1
        results.append({'p':p,'result':'PASS','exact_orders':actual,
                        'prime_divisors_p_minus_1':ff,
                        'index_3_7':(p-1)//math.lcm(a,w)})
    output = {'result':'PASS','primes':len(results),'method':'trial division; full p-1 factorization; exact order reduction',
              'results':results}
    (HERE/'prime_supply_audit.json').write_text(json.dumps(output,indent=1)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='results'}))


if __name__=='__main__':
    main()
