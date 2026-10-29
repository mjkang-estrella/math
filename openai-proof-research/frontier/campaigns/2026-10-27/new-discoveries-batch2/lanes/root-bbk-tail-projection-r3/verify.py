from check import projection, phi, x, s, Path, json, math

def direct_series(k,n,limit):
    a=[1]+[0]*limit
    for d in range(1,2*n+2,2):
        for j in range(d,limit+1): a[j]+=a[j-d]
    for h in range(2*k-1,2*k+2*n-1,2):
        for j in range(limit,h-1,-1): a[j]-=a[j-h]
    return a

checks=0
for k,n in [(2,0),(5,3),(8,3),(20,3)]:
    p,mean=projection(k,n)
    # Every pole's order divides 105 in these cases. Above the polynomial
    # part the literal series must therefore equal this projection.
    D=2*n*(k-2)-1
    offset=105*max(1,(D+105)//105)
    a=direct_series(k,n,offset+104)
    assert a[offset:offset+105]==p
    checks+=105

data=json.loads(Path(__file__).with_name('checks.json').read_text())
for case in data['cases']:
    k,n=case['k'],case['n']
    P=s.Poly.from_list(list(reversed([s.Rational(t) for t in case['projection']])),x,domain=s.QQ)
    nums=list(range(2*k-1,2*k+2*n-1,2))
    dens=list(range(1,2*n+2,2))
    # Independent residue formula using the original factors rather than
    # the cancelled cyclotomic numerator/denominator of check.py.
    for c in s.divisors(105):
        nd=[h for h in nums if h%c==0]
        dd=[d for d in dens if d%c==0]
        if len(dd)-len(nd)!=1:
            expected=s.Poly(0,x,domain=s.QQ)
        else:
            f=phi(c)
            A=s.Poly(1,x,domain=s.QQ);B=A
            for h in nums:
                if h%c: A=(A*s.Poly(1-x**(h%c),x,domain=s.QQ)).rem(f)
            for d in dens:
                if d%c: B=(B*s.Poly(1-x**(d%c),x,domain=s.QQ)).rem(f)
            scalar=s.Rational(105*math.prod(nd),math.prod(dd))
            expected=(scalar*A*s.invert(B,f)).rem(f)
        assert P.rem(phi(c))==expected
        checks+=1
out={'status':'PASS','exact_comparisons':checks,'scope':'Residue-formula and literal-series cross-checks; no full BBK proof.'}
Path(__file__).with_name('verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
