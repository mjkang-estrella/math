# F_5 = { n = R_L + 4*10^e }.  Claim: 7-smooth members are exactly 5 and 15.
M0=5291005291
assert M0==11*13*37*101*9901
H3={pow(3,u,M0) for u in range(9900)}
assert pow(3,9900,M0)==1 and pow(7,900,M0)==1 and pow(10,12,M0)==1
inv7=pow(7,-1,M0)
def in_H(V):
    x=V%M0
    for w in range(900):
        if x in H3: return True
        x=x*inv7%M0
    return False
# e>=1: n ends in 1, so 5 does not divide n; n odd; need 9n = 3^(u+2) 7^w.
hits=[(L,e) for L in range(12) for e in range(12) if in_H(10**L+36*10**e-1)]
print("residue pairs (L mod 12, e mod 12) with 9n in <3,7> mod M0:", hits)
# e=0: 9n = 10^L+35 = 5*(2^L 5^(L-1)+7); mod 7 forces w=0; need 2^L 5^(L-1)+7 = 3^k.
# For L>=3 LHS = 7 mod 8 but 3^k mod 8 in {1,3}.  L=1 -> 9 (n=5), L=2 -> 27 (n=15).
print([(L, 2**L*5**(L-1)+7) for L in (1,2)], " mod-8 values of 3^k:", {pow(3,k,8) for k in range(4)})
