# PROOF-ERRATUM.md - correction to the reviewer's own PROOF.md, section 3

PROOF.md is kept byte-for-byte as first written, before the author file was opened.
This erratum records one real error in it, found while auditing the author's endgame.
The conclusion of Theorem B is unaffected. PROOF.md must be read together with this file.

## The error
PROOF.md 3.2 says of the ABS step "the p-1 chip is taken by C_p first", and PROOF.md 3.4
gives one ABS list for all small m. That is true when the chip at p-1 is created by the
combine C_{p-2} (Case 2, a_{p-3}=1), because that combine fires before C_{p+1}. It is false
when the chip is created by the split S_{p-2} (Case 3, a_{p-2}=1): combines outrank splits,
so C_{p+1} fires BEFORE S_{p-2}. With a large pool the two orders give the same net result,
so 3.2's step formula for m>=5 stands. With a small pool they differ. The author's endgame
list has this right. Mine did not. The wrong entry is ABS m=3 under Case 3.

## Corrected exit table, from B_p(r,m,M), 0<=m<=4, M>=4, r'=r-F_{p-3}
Case 1 (non-ABS, r<F_{p-3}): as in PROOF.md.
Case 2 (a_{p-3}=1; C_{p-2} creates the chip at p-1 at once; also the pattern for p=2):
 m=2: a_p=0, chips at p-1 and p+1; C_{p+2}, C_{p+3}: B_{p+2}(r'+F_{p-1}, M-2, 1).
 m=3: C_p; a_{p+1}=2; 2 C_{p+2}, 2 C_{p+3}: B_{p+2}(r', M-4, 2).
 m=4: C_p, C_{p+1}; a_{p+1}=1, M+1; C_{p+2}, C_{p+3}: B_{p+2}(r', M-1, 1).
Case 3 (a_{p-2}=1; a_{p-2}=2 after S_p, so all combines run before S_{p-2}):
 m=2: a_p=0, a_{p+1}=1; C_{p+2}, C_{p+3} (M-2, h=1); then S_{p-2} and low relaxation; the
      chip at p-1 stays low because a_p=0: B_{p+2}(r'+F_{p-1}, M-2, 1). Same as Case 2.
 m=3: a_p=1, a_{p+1}=1; C_{p+1}: a_p=0, a_{p+1}=0, M+1; then S_{p-2} and low relaxation;
      the chip at p-1 stays low: B_{p+2}(r'+F_{p-1}, M+1, 0).   <-- CORRECTED ENTRY
 m=4: a_p=2, a_{p+1}=1; C_{p+1}: a_p=1, M+1; S_{p-2}; C_p: a_p=0, a_{p+1}=1;
      C_{p+2}, C_{p+3}: B_{p+2}(r', M-1, 1). Same as Case 2.
Validity of the corrected entry: r'<F_{p-2}, so Z(r') has maximum index <=p-3 and
Z(r')+e_{p-1} is Zeckendorf; r'+F_{p-1}<F_{p+1}; h=0<=2. Every exit is still a B_{p+2}
state with h<=2, and the assembly in 3.5 uses only that fact and the O(F_p) exit bound.

## Also tightened
PROOF.md 3.2's sentence that low and high moves "commute; priority only chooses the
interleaving" holds only when the pool is large enough that every high move stays legal.
For m>=5 that holds. For m<=4 the table above replaces it.

## Hand consistency checks added after the correction
Identity (I) with cycle data needs L := sum_{even q<=p-2} q F_{q-2} = (p+1)F_{p-3}-F_p+2.
p=4: L=2, RHS 5-5+2=2. p=6: L=2+8=10, RHS 21-13+2=10. p=8: L=2+8+30=40, RHS 72-34+2=40.
Full p=4 and p=6 orbits were traced by hand; splits per cycle 4 and 12 = F_p-1.
