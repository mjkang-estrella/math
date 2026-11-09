# Fix for GLM r4 Step 2, delta in {4,8}, e=1:  9n = 10^L + c, c = 90(delta-1)-1 in {269, 629}, L>=3.
for d in (4,8):
    c=90*(d-1)-1
    l=[L for L in range(3) if (pow(10,L,27)+c)%27==0]; r=[L for L in range(6) if (pow(10,L,7)+c)%7==0]
    assert len(l)==1 and len(r)==1 and l[0]%3!=r[0]%3   # never (a>=3 and b>=1)  => a=2 or b=0
    assert (c%8)==5
    a2 = {(9*pow(7,b,8))%8 for b in range(2)}          # a=2: 9*7^b mod 8
    b0 = {pow(3,a,8) for a in range(2)}                # b=0: 3^a mod 8
    print(f"delta={d}: c={c}, (l,r)=({l[0]},{r[0]}), a=2 residues {a2}, b=0 residues {b0}; 5 reachable? {5 in a2|b0}")
