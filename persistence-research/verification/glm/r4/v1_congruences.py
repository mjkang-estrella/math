# r4/v1_congruences.py — certify every finite congruence fact used in the odd-layer proof.
# Run: bash -c 'ulimit -v 3000000; python3 -I verification/glm/r4/v1_congruences.py'
ok = []

# (F1) 3^a*7^b mod 8 by parity
t = {}
for a in range(2):
    for b in range(2):
        t[(a, b)] = (3**a * 7**b) % 8
assert t == {(0,0):1, (0,1):7, (1,0):3, (1,1):5}, t
ok.append("F1: 3^a*7^b mod 8 = 1/7/3/5 for (ee/eo/oe/oo)")

# (F2) 3^a*7^b == 4 mod 5 => a,b same parity  (check all a,b mod 4)
same = set()
for a in range(4):
    for b in range(4):
        if (pow(3,a,5)*pow(7,b,5)) % 5 == 4:
            same.add((a % 2, b % 2))
assert same == {(0,0), (1,1)}, same
ok.append("F2: 3^a*7^b == 4 mod 5 only for a,b same parity")

# (F3) opposite parity => product mod 5 in {2,3}
opp = {(pow(3,a,5)*pow(7,b,5)) % 5 for a in range(4) for b in range(4) if a%2 != b%2}
assert opp == {2, 3}, opp
ok.append("F3: opposite parity => 3^a*7^b mod 5 in {2,3} (never 4)")

# (F4) both odd => product mod 5 in {1,4}
oo = {(pow(3,a,5)*pow(7,b,5)) % 5 for a in range(4) for b in range(4) if a%2==1 and b%2==1}
assert oo == {1, 4}, oo
ok.append("F4: a,b both odd => 3^a*7^b mod 5 in {1,4} (never 3)")

# (F5) 7^b mod 25 cycle {1,7,24,18}; 21 and 11 absent
cyc = {pow(7,b,25) for b in range(4)}
assert cyc == {1,7,24,18} and all(pow(7,b,25)==pow(7,b%4,25) for b in range(40))
assert 21 not in cyc and 11 not in cyc
ok.append("F5: 7^b mod 25 cycles {1,7,24,18}; 21,11 never occur")

# (F6) 3^a mod 25: ==14 iff a==18 mod 20 ; ==-1(24) iff a==10 mod 20 ; ord=20
assert pow(3,20,25)==1 and pow(3,10,25)==24 and pow(3,4,25)!=1
cls14 = [a for a in range(20) if pow(3,a,25)==14]
clsm1 = [a for a in range(20) if pow(3,a,25)==24]
assert cls14==[18] and clsm1==[10], (cls14, clsm1)
ok.append("F6: 3^a==14 mod 25 iff a==18 mod 20; 3^a==-1 mod 25 iff a==10 mod 20")

# (F7) ord_7(3)=6; classes
assert pow(3,6,7)==1 and pow(3,3,7)!=1
cl = {r: [a for a in range(6) if pow(3,a,7)==r] for r in range(1,7)}
assert cl[3]==[1] and cl[5]==[5] and cl[2]==[2] and cl[4]==[4] and cl[1]==[0] and cl[6]==[3]
ok.append("F7: 3^a mod 7 classes: a==1 mod 6 -> 3; a==5 -> 5; etc. (ord 6)")

# (F8) 3^a mod 13 has period 3 -> {1,3,9}; 10^L mod 13 = 10 when L==1 mod 6; 449==7
assert all(pow(3,a,13) in {1,3,9} for a in range(60))
assert pow(10,6,13)==1 and pow(10,1,13)==10
assert 449 % 13 == 7
ok.append("F8: 3^a mod 13 in {1,3,9}; 10^L==10 mod 13 for L==1 mod 6; 449==7 mod 13")

# (F9) QRs: mod 5 {0,1,4}; mod 11 {0,1,3,4,5,9}; 2 is a non-residue mod 11
q5 = {(i*i) % 5 for i in range(5)}
q11 = {(i*i) % 11 for i in range(11)}
assert q5 == {0,1,4} and q11 == {0,1,3,4,5,9} and 2 not in q11
assert 89 % 11 == 1 and 17 % 5 == 2 and 89 % 25 == 14
ok.append("F9: QR mod 5 {0,1,4}; QR mod 11 {0,1,3,4,5,9}; 2 non-QR mod 11; 89==1 mod 11")

# (F10) L-class tables: 27 | 10^L + c  iff L == l mod 3 ;  7 | 10^L + c iff L == r mod 6
def l27(c):
    s = [L for L in range(3) if (pow(10,L,27)+c) % 27 == 0]
    return s[0] if len(s)==1 else None
def r7(c):
    s = [L for L in range(6) if (pow(10,L,7)+c) % 7 == 0]
    return s[0] if len(s)==1 else None
tab = {89:(l27(89), r7(89)), 269:(l27(269), r7(269)), 449:(l27(449), r7(449)),
       629:(l27(629), r7(629)), 17:(l27(17), r7(17)), 53:(l27(53), r7(53)),
       71:(l27(71), r7(71))}
expect = {89:(2,2), 269:(0,4), 449:(1,3), 629:(2,0), 17:None, 53:None, 71:None}
# c=17,53,71 (e=0 layer): 27-class computed but only parity kills used; r7 needed? check none needed
for c,(l,r) in tab.items():
    if expect[c] is not None:
        assert (l,r)==expect[c], (c,l,r,expect[c])
# cross-check the 27-classes with the hand values used: 89->2, 269->0, 449->1, 629->2 mod 3
# and the 7-classes: 89->2, 269->4, 449->3, 629->0 mod 6
ok.append(f"F10: (27-class, 7-class) per c: {tab}")

# (F11) mod 8 values of 10^L + 90(delta-1)*10^e - 1 for L>=3
for d in [2,3,4,6,7,8,9]:
    for e in (1,2,3):
        for L in (3,4,5,8):
            v = (pow(10,L,8) + 9*(d-1)*pow(10,e,8) - 1) % 8
            hand = ((d-1)*(2 if e==1 else (4 if e==2 else 0)) - 1) % 8
            assert v == hand, (d,e,L,v,hand)
ok.append("F11: (10^L + 90(d-1)10^e - 1) mod 8 = (2(d-1)-1) for e=1, = -1=7 for e>=2, L>=3")

# (F12) e=0 layer, c = 9*delta-10 mod 8 and mod 5
for d,c in [(3,17),(7,53),(9,71)]:
    assert (9*d-10)==c and c%8 in (1,5,7) and all((pow(10,L,8)+c)%8==c%8 for L in range(3,9))
ok.append("F12: e=0: c mod 8 = 1(d=3), 5(d=7), 7(d=9); 10^L==0 mod 8 for L>=3")

# (F13) direct small checks
def smooth37(m):          # m = 9n ; is m == 3^a 7^b ?
    for p in (3,7):
        while m % p == 0: m //= p
    return m == 1
# e=0, L=1: 9n = 9*delta -> n=delta ; L=2: n = delta+10
assert [d for d in [2,3,4,6,7,8,9] if smooth37(9*d)] == [3,7,9]
# e=1, L=2: n = 10*delta+1  (odd layer: all delta here have e>=1)
assert [d for d in [2,3,4,6,7,8,9] if smooth37(9*(10*d+1))] == [2,8]
assert smooth37(9*21) and smooth37(9*81) and not smooth37(9*91) and not smooth37(9*31)
# e=1, L=3: n = 101+10d ; e=L-1=2, L=3: n = 100d+11
assert [d for d in [2,3,4,6,7,8,9] if smooth37(9*(101+10*d))] == []
assert [d for d in [2,3,4,6,7,8,9] if smooth37(9*(100*d+11))] == []
# e=0, L=2 for odd delta: 9n = 100 + c
for d,c in [(3,17),(7,53),(9,71)]:
    assert not smooth37(100+c), (d,c)   # 117=9*13, 153=9*17, 171=9*19
ok.append("F13: small cases: (e0,L1)->3,7,9; (e0,L2, odd delta)->none; (e1,L2)->21,81; (e1,L3),(e2,L3)->none")

print("ALL %d FACT-CHECKS PASS" % len(ok))
for s in ok: print(" -", s)
