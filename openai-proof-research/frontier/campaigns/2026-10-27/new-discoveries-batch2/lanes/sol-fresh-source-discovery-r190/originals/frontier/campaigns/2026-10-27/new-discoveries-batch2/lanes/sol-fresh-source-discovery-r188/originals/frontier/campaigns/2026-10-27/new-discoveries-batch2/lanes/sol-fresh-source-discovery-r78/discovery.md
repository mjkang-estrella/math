# r78 — Elgin–Reading–Stella factorial denominators: unresolved

Status: research notes, candidate/unreviewed reductions only. No complete proof or refutation, no discovery credit, no formalization or paper.

## Selection and duplicate gate

Read applicable ancestor and batch AGENTS, current NEXT, both ledgers/context files, and the supplied current-registry metadata. `context-reading.json` preserves the actual JSON consumed and hashes. Counts read: 7/30 additional, 37/60 overall. No shared files changed.

Before mathematical investment, searched **all campaign dates**, all `.md` and `.json` filenames without restricting report basenames (thus including FINDINGS), with `rg -l` first, followed by bounded matching lines. Logs are `duplicate-filenames.txt`, `duplicate-sections.txt`, `cluster-duplicate-filenames.txt`, and `cluster-duplicate-sections.txt`. Terms included authors Elgin/Reading/Stella, Lundström/Saud Maia, titles, arXiv numbers2404.11381/2511.14672, record371551, scatcoef, and factorial-formula terms. The bare number371551 also hits unrelated Git hashes; those are not mathematical duplicates. Registry JSON and the old MathDB catalogue contain cluster titles, but the retrieved matches did not identify an earlier campaign proof attempt on C4. This is a bounded lexical gate, not global absence certification.

Three exact primary assertions screened:

1. Lundström–Saud Maia Leite, published EJC133(2026)104304, Conjecture6.2, log-concavity of the order-polytope face vector of a polygon face lattice. **Exclude.** Campaign r65 already screened its stronger crown Conjecture3.7. Latest arXiv2504.05123v5 Theorem3.12 proves the crown face-vector statement; Section6 multiplies its f-polynomial by (1+t)^2 for the polygon face lattice. Actual current theorem and proof body read, not just the earlier lane report. The first publisher-reprint request returned403; no bypass was attempted.
2. Elgin–Reading–Stella C15, tau(kd,ke;k)=tau(d,e;1)^k/k! for coprime d,e. **Exclude.** Actual published Burcroff–Lee–Mou–Musiker–Reineke Theorem1.4 includes C15; Section6 proves the stronger coefficient convolution by expanding exp(g log(F)/(bc)).
3. Elgin–Reading–Stella **C4**, the full factorial-denominator assertion below. Survives the preceding specific subsumption screen: published follow-up after Theorem1.4 explicitly leaves C4, C12, C13 unresolved. Selected for sustained mathematical work. Its current priority is nevertheless **HOLD**, not certified fresh.

The general Alikhani–Peng domination-unimodality statement was also read in Omar2601.14494v1 Conjecture1 as a preliminary lead; it was not selected or computed on.

## Exact source target and provenance

Elgin, Reading, Stella, *Cluster scattering coefficients in rank2*, arXiv2404.11381 latest observed v4, revised27July2025. Actual author/publisher HTML:
https://amj.math.stonybrook.edu/Articles/250110-Reading/index.html
The publisher full issue search also locates C4 on printedp116:
https://armj.math.stonybrook.edu/Issues/Volume12Issue1Year2026.pdf

For every pair of positive integers i,j, let tau(i,j) be the wall-function coefficient defined by the rank2 cluster scattering diagram in source Section2, with positive exchange parameters b,c, and

    g = gcd(ib,jc)/gcd(i,j).

By the now-proved polynomiality assertion this has a polynomial representative in Q[b,c,g]. **C4 asks whether max(i,j)! tau(i,j) belongs to Z[b,c,g] for every i,j>0.** This is monomial coefficient integrality, not integer-valuedness at positive integral b,c and their actual gcd. No restriction to primitive (i,j), diagonal rays, or fixed exchange matrix is permitted.

Closest actual public theorem body:
Burcroff, Lee, Mou, Musiker, Reineke, *Cluster scattering diagrams via quiver moduli and tight gradings*, arXiv2511.14672v1 (only version shown by current abstract record); published28July2026, JLMS DOI10.1112/jlms.70642.
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.70642
Read its definitions2.1–2.5, Theorem1.4 and following remark, Theorem4.10, Corollary4.16, and the Section6 polynomiality/convolution proof. These are existing theorems, not lane discoveries. In particular tight-grading positivity proves integrality in initial coefficient variables; it does **not** immediately prove C4 after substituting binomial polynomials in b,c.

## Full-scope route: remove the gcd variable

Fix coprime d,e>0 and write m=max(d,e). The published change-of-lattice formula gives

    1+sum_{k>=1} tau(kd,ke) t^k
       = (1+sum_{k>=1} rho(kd,ke)t^k)^(g/(bc)).

Here rho is for the standard diagram with initial functions (1+x)^c and (1+y)^b. Define A_k=rho(kd,ke)/(bc), a polynomial in Q[b,c]. The following equivalence is an ordinary **helper**, not a resolution:

    C4 for every k on this ray
       iff (mk)! A_k is in Z[b,c] for every k.

Proof of the forward direction: specialize the polynomial identity at g=bc. This gives rho. Since every tau polynomial has a factor g, after specialization its integral coefficients divided by bc remain integral. This is a formal polynomial specialization; it is not a claim that the physical gcd equals bc for all b,c.

For the reverse direction, expand the power by the binomial theorem. Given a finitely supported tuple a_s>=0 with sum s*a_s=k and n=sum a_s, its contribution is

    [product_{r=0}^{n-1}(g-rbc)] * product_s A_s^a_s / product_s a_s!.

If B_s=(ms)! A_s is integral, multiplication by (mk)! makes this an integral polynomial, because

    (mk)! / product_s (a_s! ((ms)!)^a_s)

counts partitions of mk labeled objects into a_s unlabeled blocks of size ms. Sum over the finitely many tuples. This proves the implication uniformly, including nonprimitive coefficients k>1. The checker tests1626 of these block-count divisibilities, but the combinatorial argument, not these tests, proves the helper.

## Exact remaining congruence

Let P partition i and Q partition j; let (z)_r=z(z-1)...(z-r+1). The published theorem expresses

    A_(i,j) = sum_{P,Q} lambda(P,Q)
              product_{p in P} binom(c,p) product_{q in Q} binom(b,q)/(bc).

The lambda are actual nonnegative integer counts of tight gradings. Consequently

    N_(i,j) := i! j! A_(i,j)
      = sum lambda(P,Q) [i!/product p!][j!/product q!]
            [product (c)_p/c][product (b)_q/b]

is in Z[b,c]. Each partition is nonempty, so division by b and c removes polynomial factors, with no new denominator. Each factorial quotient is a multinomial integer. This establishes only the elementary i!j! bound.

**The unresolved uniform assertion is exactly**

    min(i,j)! divides every monomial coefficient of N_(i,j), for all i,j>0.

Together with the preceding equivalence, this would prove the entire source C4. There is no proof here of this extra divisibility. Positive integer lambda and the degree bounds alone do not imply it.

## Actual tight-grading cancellation, not large enumeration

`check.py` independently implements source Definition4.5 compatibility and the negative-sign tightness condition of Definition4.8, on the maximal Dyck path for (d1,d2)=(4,5) with total vertical grading3 and horizontal grading4. The Bezout condition is3*5-4*4=-1. It streams all1225 weak-composition pairs, retaining13 tight gradings, groups their partition types into lambda, reconstructs A_(3,4), and agrees **as a rational polynomial** with the already-public C10 formula:

    A_(3,4) = (b-1)*((4c-3)(b-1)-1)*((4c-3)(b-1)-2)/24.

Thus24 A_(3,4) is integral. This is a routine known-formula diagnostic, not a newly solved parameter instance. Its top b^3 c^2 coefficient after multiplying by24 is16. In contrast, the singleton partitions P=(3), Q=(4) have lambda=1 by public Corollary4.16; their individual contribution is binom(c,3)binom(b,4)/(bc), whose scaled top coefficient is1/6. In N_(3,4), the singleton top coefficient1 combines with other partitions to give96, divisible by3!=6. Therefore a **termwise** divisibility proof using the positive tight-grading formula is false. Cross-partition congruences are essential.

## Strongest classical shortcuts tested and rejected

* Integer-valued polynomial interpolation is insufficient. The artificial polynomial g*binom(b,4)*binom(c,3) has b-degree4, c-degree3, g-degree1 and is integral at every integral b,c,g. It obeys the relevant simple degree/factor conditions at (i,j)=(4,5), yet multiplying by5! leaves top coefficient5/6. This artificial polynomial is not a scattering coefficient, nor a counterexample to C4. It isolates the insufficiency of those hypotheses.
* A generic Poisson-algebra closure proof at denominators1/max(i,j)! fails. In the algebra with bracket [X^iY^j,X^rY^s]=(is-jr)X^(i+r)Y^(j+s), bracket the allowed terms X^5Y/5! and XY^5/5!. The coefficient multiplied by6! is24*6!/(5!)^2=6/5. The proposed lattice is not bracket closed. This is not the full cluster construction and is not a source refutation.
* The authors' provided Sage code was fetched and read but not executed (Sage is unavailable); its pickled `.sobj` data was not loaded. No claim of reproducing all degree20 source experiments.

The most plausible remaining route is to find a signed labeled interpretation of N_(i,j) with enough free symmetry to force the min(i,j)! divisor, or prove those prime-power congruences directly across partition types. No free symmetric-group action has been constructed: singleton terms show why an action confined to each partition type cannot suffice. No claim that a root-of-unity, BCH, or classical interpolation theorem supplies the missing bridge.

## Current registries and exact eligibility hold

Read-only searches of the supplied complete dated inventories (Omega70af54071bfd4ac098619a9db8c16bb6f7aced11, OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, observed17:20:12UTC) are preserved in the two path-match files. Matching broad rank-two and Takagi names are unrelated finite-group/quantum records; no direct cluster-scattering filename was found by those terms. This does not audit all bodies or identify disguised equivalents.

A single ordinary public HTTP read per repository page at17:56UTC recovered currentOid Omega75fa71fb84c19580a0ea89b3dc7c8158f7aa7446 and unchanged OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. **Omega has advanced beyond the complete supplied inventory.** No current full tree or change-body audit was obtained. Therefore current-prior/freshness remains HOLD; the old complete tree is not presented as current HEAD. No Git/API operation, retries, proxy, or cache mutation occurred.

The published follow-up is positive evidence about its July2026 unresolved scope, not proof of present novelty. Akagi's earlier long paper was located but web body searches timed out; no complete Akagi/follow-up audit or global priority clearance is claimed. Author/title/record searches did not locate a later C4 resolution, which alone is not absence evidence.

## Strongest referee objection and falsifier

Decisive objection: the min(i,j)! coefficient divisibility has not been proved. One small cancellation identity, a formal transport lemma and two failed generic shortcuts do not address the uniform congruence. Even a future proof would require current-public-body and routine-subsumption review before substantive eligibility.

A source falsifier requires an actual tau polynomial at some i,j whose coefficient denominator does not divide max(i,j)!, with its exact scattering construction verified. A generic Poisson lattice failure, fake integer-valued polynomial, or individual summand failure does not qualify. A counterexample to the stronger A bound, if literally established for actual rho, would also refute universal C4 by the proved equivalence.

Disposition: unresolved, credit0; no PROOF.md, Lean, paper, or acceptance recommendation.
