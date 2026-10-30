# Restricted Bell real-rootedness: unresolved, credit 0

One primary candidate screened and pursued, below the cap of four. No source theorem or refutation completed. No PROOF.md, Lean, paper, nomination or acceptance. Counts observed 6/30 additional and 36/60 total; root owns all credit.

## Literal source and scope

Moll–Ramírez–Villamizar, *Combinatorial and Arithmetical Properties of the Restricted and Associated Bell and Factorial Numbers*, arXiv:1707.08138v1/v2, Section 6.1, Conjecture 6.4, PDF p14. Define S_m(n,k) as the number of partitions of [n] into k nonempty blocks each of size at most m. The source defines B_{n,≤m}(x)=sum_k S_m(n,k)x^k and asserts that all its zeros are real and nonpositive if m is not 3 or 4. The intended positive-integer caps are m=1,2 and every m>=5, for all n>=0. These are fixed combinatorial definitions, not free weights. Counterexamples at m=3 or4 would not refute the conjecture; proving one cap would not settle its full positive direction.

Read actual source introduction/definition/recurrence (1.2), Sections4 and6, Theorems6.1–6.3 and their proofs, and the conjecture. Both retrieved versions retain the same conjecture. The current arXiv abstract page lists July25/31,2017 v1/v2. The downloaded PDFs have a December14,2024 internal typesetting date; preserve those exact bytes and distinguish that from submission chronology. The publisher search-index excerpt labels the same displayed claim Conjecture6.2, p710. Full publisher PDF returned403 to web fetch; no retry/bypass. Consequently no authenticated full final-version comparison or final journal-date assertion is made.

## Closest actual primary bodies

Jung et al., *The r-Bessel and restricted r-Bell numbers*, Australas. J. Combin.70(2)(2018),202–220: Definition4.1, Eq(8), Theorem4.2 and full Hermite proof on pp208–209 read. Its r=0 EGF is exp(x(z+z²/2)); this is cap2, not cap r or arbitrary cap m. Its r parameter distinguishes specified elements. The old cap2 case receives no credit and that theorem does not prove the selected all-cap claim.

Caicedo–Moll–Ramírez–Villamizar, EJC26(2)(2019)#P2.20, actual published pp21–23 Theorems38–40 and proof read. Theorem38 gives the cap-m EGF, with r=0 giving exp(x sum_{j=1}^m z^j/j!). Theorem39 and Dobinski Theorem40 give identities, not an all-cap real-rootedness theorem in the inspected bodies. Bényi–Ramírez arXiv:1804.03949v1, actual Section2/Theorem3 determinant and proof read: arbitrary-S restricted Bell determinant identity, not a zero-location conclusion. These were antecedent comparisons, not additional candidate projects. No broad assertion of absence from every page or all citing literature.

A mistaken guessed arXiv identifier1810.09645 downloaded a liquid-crystal PDE paper as sources/extensions.pdf. It is explicitly unrelated and not evidence. The correct actual EJC body is sources/extensions-correct.pdf. Both retrievals are preserved transparently; only the correct paper is used.

## Current registry comparison

Five heads freshly retrieved on2026-10-29 around14:37UTC; all unchanged from r45:

- Omega dev13540e54dcb7e367c6799640ec15b707fcf2bb18.
- Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5.
- OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
- MColbrook/AIM8729eab98bafe409b66c5e39253bf56569a62327.
- Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a.

Reused complete untruncated hashed scopes from r45, precisely D5, Problems, Omega-main tree, OpenAI preprints, AIM tree and Count tree, with entry counts and pathname matches in registry-screen.json. These are named scopes, never a whole-dev search or semantic completeness claim. Read actual matching claim/definition/proof bodies in the freshly downloaded public-bell.lean, public-qbell.lean and public-restricted.lean, plus their available problem notes. Respectively they concern Bernoulli-weighted ordinary Bell profile nonvanishing, Kurkov reversed q-Bell rows, and bivariate marked clique instability. Their literal definitions and endpoints differ from cap-m block-count real-rootedness. They neither prove nor refute the selected claim. Other pathname matches are recorded but not all body-read; this is a bounded comparison, not novelty clearance. Search hits/open labels/absent matches do not establish novelty.

## Concrete route and exact method obstruction

The EGF gives an exact coefficient recurrence by taking the block containing the distinguished element:

S_m(n,k)=sum_{j=1}^{min(m,n)} binom(n-1,j-1) S_m(n-j,k-1).

It agrees with the source differential-delay recurrence

B_{n+1}=xB_n+xB'_n-binom(n,m)xB_{n-m}.

A possible route was to transfer classical Bell real-rootedness through the natural diagonal coefficient map λ_k=S_m(n,k)/S(n,k), with λ_0=0 for n>0. At n=m+1=6, only the one-block partition is removed: λ_1=0 and λ_k=1 for2<=k<=6. Thus this map takes (1+x)^6, whose only root is−1, to

Q(x)=(1+x)^6−1−6x=x²(x⁴+6x³+15x²+20x+15).

Q has no real root except0: the function y↦y^6 is strictly convex on the real line, so its tangent at y=1 lies strictly below it at every other point. Equivalently Q''=30(1+x)^4 with Q(0)=Q'(0)=0, and integrate on either side of0. The zero at0 has multiplicity2, so the other four roots are nonreal. This proves that this exact diagonal map fails to preserve real-rootedness, including on polynomials with all zeros negative. No invocation of a general multiplier-preserver theorem can justify this route.

In contrast the actual B_{6,≤5}=x²(x⁴+15x³+65x²+90x+31) has four distinct negative nonzero roots by exact Sturm count and positive coefficients. The method obstruction is therefore explicitly not a source counterexample. It does not rule out a map using special properties of Bell inputs, a coupled interlacing invariant, or another construction. The source's subtraction term remains the precise obstacle to the naive classical Bell induction; no uniform sign control at the old roots has been proved here.

## Bounded checks and limits

Run `bash run.sh python3 check.py` and `bash run.sh python3 route.py` (Python3+SymPy). Each process is capped at AS512MiB, CPU210s, wall230s, BLAS/OMP/MKL1, timeout process-group TERM then KILL. No heavy enumeration, numerical root solver or numerical-evidence proof.

check.py builds490 rows for caps5,6,7,8,9,10,12 throughn70. For n10..70 (427 cases) Newton sums of the monic polynomial after removing x^ceil(n/m) produce the Hermite moment matrix H_ij=s_{i+j}. Every2x2 principal minor passes the necessary nonnegativity test. This weak test is not a full PSD or real-rootedness certificate. At n10,15,20,25,30 for those7caps, all35 exact Sturm root counts equal the deflated degree. route.py checks120 rows against the independent differential-delay recurrence; focused exact Sturm counts at (m,n)=(5,40),(5,60),(6,40),(6,60) equal32,48,33,50. It also checks the generic-operator obstruction and the actual cap5,n6 contrast. Finite passes are not the all-n/all-m theorem.

## Strongest objection, falsifier, exact remaining gaps

The strongest objection is decisive: there is no complete qualifying mathematical outcome. The route's hoped-for general preservation property is false on the explicit real-rooted input above; the remaining finite positive evidence supplies no uniform substitute. No substantive or novelty PASS is requested.

A source refutation requires an actual positive-integer m>=5 and n with a certified nonreal zero of the literal B_{n,≤m}, not a failed multiplier symbol or another restricted Bell definition. A positive solution requires all such m,n, including repeated zero factors and all nonzero roots. Missing: a uniform coupled sign/interlacing or equivalent positivity argument, authenticated final published source comparison, and broader citation/semantic prior-art review if mathematics ever closes. No parameter-family proof, helper or classical cap2 rediscovery should be counted. No further grid expansion is recommended absent a new mathematical mechanism.
