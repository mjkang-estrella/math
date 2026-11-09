# MathDB 382141: exact ordinary character-sum equality lead

Source 2302.04022, Conjecture 6.1, requires a STRICT inequality for odd n>=7, {n-1,n} subset I subset {2,...,n}. Take n=23 and I={19,22,23}.

For a k-cycle with m=n-k fixed points, the standard character-polynomial identities are

    chi_(n-2,1^2) = ((m-1)(m-2))/2 - [k=2], dimension (n-1)(n-2)/2;
    chi_(n-2,2)   = m(m-3)/2 + [k=2], dimension n(n-3)/2.

Conjugation of partitions multiplies these characters by (-1)^(k-1). A k-cycle class has n!/[k(n-k)!] elements. The source's normal-Cayley eigenvalue formula is the class-size weighted normalized-character sum. For n=23 the dimensions are 231 and 230. At lengths 19,22,23 the hook characters are 3,0,1 and the conjugate two-row characters are 2,1,0. Therefore, after dividing by 23!, the four quantities in the conjecture are

    lambda_(3,1^20) = (3/(19*24)+1/23)/231;
    lambda_(1^23) = 1/(19*24)-1/22+1/23;
    lambda_(21,1^2) = (3/(19*24)+1/23)/231;
    lambda_(2^2,1^19) = (2/(19*24)+1/22)/230.

All are 25/115368, hence all actual values are 5602076992512000000. Strict inequality fails. scripts/certificates.py checks the exact rational arithmetic; scripts/characters.py independently searches all admissible I for odd n=7..21, and a precisely recorded Gray-code prefix at n=23. The first equality is mask 131072, I={19,22,23}. The prefix contains 262144 masks; the full n=23 space of 1048576 masks was NOT completed.

Mechanism: if I contains an even length besides n-1, the hook comparison is strict. Otherwise let A be the target hook value, C the sign value, D the conjugate-two-row value, and d=n(n-3)/2. Then C-A+d(D-A)=0. Equality of all three reduces, after cancelling n!, to

    sum over odd k in I of (2n-k-3)/(n-k)! = n-2.

The obligatory k=n term is n-3. Choosing only k=n-4 in addition contributes (n+1)/24, which is 1 exactly at n=23. This explains the witness rather than merely reporting a numerical coincidence.

The source's actual character tables, Lemma 4.3(d), eigenvalue formula and Conjecture 6.1 were read. The actual journal body (JCTA 206, 2024, 105885) has not been read: its DOI returned only a redirect page. Same-author follow-up 2607.29018v2 was retrieved; its normal-Cayley definition/eigenvalue formulas and principal Aldous-property results were inspected, not its whole proof corpus. It addresses a different Aldous-property question, but this limited inspection does not rule out an implicit characterization subsuming our tie. Registry path screens are not an actual proof-file audit. Further journal, same-author and citing-body review is required before claiming novelty.

There is no literal Lean endpoint. Required formal bridges include the four actual irreducible Specht representations, their dimensions/characters on these classes, and the normal-Cayley eigenvalue formula. A theorem about four arithmetic expressions would be a surrogate, so none is submitted as a solution. Credit zero; root must decide whether to reserve/fund these gaps.
