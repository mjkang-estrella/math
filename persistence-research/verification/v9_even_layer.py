# Independent short proof-certificate: for delta in {2,4,6,8}, L>=4,
# 10^L + c (c = 9*delta-10) is never 2^t 3^a 7^b.  All checks are finite residue facts.
cases={2:(8,3,1),4:(26,1,13),6:(44,2,11),8:(62,1,31)}   # c, s, c''  (c = 2^s c'')
for d,(c,s,c2) in cases.items():
    assert c==2**s*c2 and c2%2 and c%9==8
    # (1) 27 | 10^L+c  iff L = l mod 3 ;  7 | 10^L+c iff L = r mod 6  (ord_27 10 = 3, ord_7 10 = 6)
    ls=[L for L in range(3) if (pow(10,L,27)+c)%27==0]; rs=[L for L in range(6) if (pow(10,L,7)+c)%7==0]
    assert len(ls)==1 and len(rs)==1 and ls[0]%3!=rs[0]%3      # => never (a>=3 and b>=1)
    r=rs[0]
    # For L>=4 (L>s, and 5^L | ...):  2^(L-s) 5^L = (3^a 7^b) - c''  with  2^(L-s) || that.
    # Case b=0: X = 3^a. Need 3^a = c'' mod 5 -> a mod 4 class; then v2(3^a - c'') from 3^a mod 32.
    A=[a for a in range(4) if (pow(3,a,5)-c2)%5==0]
    for a0 in A:
        vals={((pow(3,a0+4*k,64)-c2)%64) for k in range(16)}         # 3^a mod 64 depends on a mod 16
        v2s={(v & -v).bit_length()-1 if v else 99 for v in vals}
        print(f"delta={d} b=0: a≡{a0} mod 4, possible v2(3^a-c'')={sorted(v2s)} -> L-s in that set")
    # Case a=2: X = 9*7^b, b>=1
    B=[b for b in range(4) if (9*pow(7,b,5)-c2)%5==0]
    for b0 in B:
        vals={((9*pow(7,b0+4*k,64)-c2)%64) for k in range(16)}
        v2s={(v & -v).bit_length()-1 if v else 99 for v in vals}
        Ls=sorted(s+v for v in v2s)
        print(f"delta={d} a=2: b≡{b0} mod 4, v2 in {sorted(v2s)} -> L in {Ls}; need L≡{r} mod 6, L>=4:",
              [L for L in Ls if L>=4 and L%6==r])
# delta=2, b=0 has v2 large possible (3^a ≡ 1 mod 64 when 16|a), so use ord_{5^L}(3)=4*5^(L-1) | a, a < 2.1L:
print("delta=2 b=0: 5^L | 3^a-1 needs 4*5^(L-1) | a, but 3^a < 10^L => a < 2.1L; 4*5^(L-1) > 2.1L for L>=2:",
      all(4*5**(L-1)>2.1*L for L in range(2,200)), "(and 5^(L-1)·4 is the exact order: 3 is a primitive root mod 25)",
      pow(3,4,25)!=1 and pow(3,20,25)==1 and pow(3,10,25)!=1)
