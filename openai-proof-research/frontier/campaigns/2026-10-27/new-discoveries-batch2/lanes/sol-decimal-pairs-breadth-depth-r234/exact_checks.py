from pathlib import Path
import json
L=Path(__file__).resolve().parent
def reverse(n):return int(str(n)[::-1])
def digits(n):return list(map(int,str(n)[::-1]))
def certificate(a,b):
    x,y=digits(a),digits(b)
    conv=[sum(x[j]*y[i-j] for j in range(len(x)) if 0<=i-j<len(y)) for i in range(len(x)+len(y)-1)]
    c=a*b; ds=digits(c); rows=[]; carry=0
    for i in range(max(len(conv),len(ds))):
        s=conv[i] if i<len(conv) else 0
        digit=ds[i] if i<len(ds) else 0
        outgoing=(s+carry)//10
        assert s+carry==digit+10*outgoing
        rows.append({'i':i,'convolution':s,'incoming':carry,'digit':digit,'outgoing':outgoing});carry=outgoing
    assert carry==0
    assert a%10 and b%10 and c%10
    assert reverse(a)*reverse(b)==reverse(c)
    return {'A':a,'B':b,'C':c,'Astar':reverse(a),'Bstar':reverse(b),'Cstar':reverse(c),'A_palindrome':a==reverse(a),'B_palindrome':b==reverse(b),'rows_low_to_high':rows,'polynomial_product':conv,'product_digit_polynomial':ds,'polynomial_equal':conv==ds}
def run():
    a=7*(10**15+10**7+1);b=858088
    z=certificate(a,b)
    assert not z['A_palindrome'] and not z['B_palindrome'] and not z['polynomial_equal']
    assert z['polynomial_product'][0]==56 and z['product_digit_polynomial'][0]==6
    z['reversed_certificate']=certificate(reverse(a),reverse(b))
    z['seed']=certificate(7,858088)
    # Separate structural mechanism: inflate both members of the classical (7,88).
    aa=7*sum(10**(3*i) for i in [0,1,3]);bb=88*sum(10**(3*i) for i in [0,4,9])
    zz=certificate(aa,bb)
    assert not zz['A_palindrome'] and not zz['B_palindrome'] and not zz['polynomial_equal']
    z['two_factor_table1_control']=zz
    # Finite diagnostic only, not an arbitrary-length theorem.
    z['finite_inflations_checked']=0
    for m in range(7,16):
        for n in range(m+7,m+18):
            if n==2*m:continue
            q=certificate(7*(1+10**m+10**n),b)
            assert not q['A_palindrome'] and not q['B_palindrome'] and not q['polynomial_equal']
            z['finite_inflations_checked']+=1
    (L/'exact-checks.json').write_text(json.dumps(z,indent=2)+'\n')
    print({k:z[k] for k in ['A','B','C','Astar','Bstar','Cstar','finite_inflations_checked']})
if __name__=='__main__':run()
