# Proposed disposition: classical-corollary exclusion, credit 0

Root derived a complete ordinary proof of Ferreira–Simon Conjecture 1 in
PROOF.md, with 2 exact symbolic identities, 45 high-precision reciprocal-moment
checks and 27 independent Bessel/Laplace checks. Before any formal investment,
a concrete classical same-object product formula was found. This note gives
the full bridge. Independent adjudication is requested; no acceptance/count.

## The actual primary source

Loyal Durand, *Product formulas and Nicholson-type integrals for Jacobi
functions. I: Summary of results*, SIAM J. Math. Anal. 9(1) (1978), 76–86,
DOI https://doi.org/10.1137/0509007, §5.1, equations (5.2)–(5.3), printed p.84.

Actual author-uploaded journal PDF read through the public web PDF reader:
https://www.researchgate.net/profile/Loyal-Durand/publication/243093738_Product_Formulas_and_Nicholson-Type_Integrals_for_Jacobi_Functions_I_Summary_of_Results/links/5a4ac9cf0f7e9ba868aff84a/Product-Formulas-and-Nicholson-Type-Integrals-for-Jacobi-Functions-I-Summary-of-Results.pdf

The reader supplies 12 PDF pages and the genuine printed journal body, including
§3.2's hypotheses, §5.1 and the footnote correcting the factor in the 1975
predecessor. Shell retrievals of both this URL and SIAM return 403; those access
failures are recorded honestly. No local PDF byte hash or visual inspection of
this page is claimed. Web PDF text is partially garbled in its math; the exact
m=0 specialization below is independently checked against the derived identity.
An independent reviewer should confirm the original display and its constants.

Durand's (5.2), specialized to m=0 and with q denoting his nu, is

    K_q(x) K_q(y)/(xy)^q
      = 2^(q-1) Gamma(q)/Gamma(2q)
          integral_0^infinity w^(-q) K_q(w) sinh(phi)^(2q) dphi,
    w=sqrt(x^2+y^2+2xy cosh(phi)).                              (D)

The apparent singular coefficient at q=0 is removable. We use q=-b in
(-1/2,0), never q=0. The required range is directly inside the derivation:
Durand's §3.2 (3.5) assumes Re(alpha)>0, and §5.1 puts q=alpha-1/2.
For m=0 its other parameter conditions are satisfied in the confluent limit.
Thus q>-1/2, not merely q>=0. Alternatively (D) is analytic in q on Re q>-1/2
after its removable normalization is simplified, so continuation from positive
q would also be valid. There is no divergent near-zero integral: 2q>-1.

## Normalize and change variables

Set q=-b, 0<b<1/2. Gamma duplication and K_(-b)=K_b give

    2^(-b-1) Gamma(-b)/Gamma(-2b)
       = 2^b sqrt(pi)/Gamma(1/2-b).

Let f_b(s)=2 s^(b/2) K_b(2sqrt(s))/Gamma(b), the literal Laplace transform
of 1/Gamma(b) (from the defining Gamma integral or DLMF 10.32.10 with order -b).
Take x=2sqrt(lambda u), y=2sqrt(lambda(1-u)), c=2sqrt(u(1-u)). Equation (D)
becomes

    f_b(lambda u) f_b(lambda(1-u))
      = [2/B(b,1/2-b)] integral_0^infinity
          f_b(lambda(1+c cosh(phi))) sinh(phi)^(-2b) dphi.        (E)

For W~Beta(b,1/2-b), W=sech(phi)^2 has precisely the measure

    [2/B(b,1/2-b)] sinh(phi)^(-2b) dphi.

Thus (E), by uniqueness of Laplace transforms, is exactly

    u/G_b + (1-u)/G_b =d (1+c/sqrt(W))/G_b,

with independence on each side. This is the entire conditional identity of
PROOF.md §1, obtained by direct substitution in a 1978 same-function theorem.

## Finish the exact source conjecture

For independent A1,A2~Gamma(a), H1,H2~Gamma(b), put G=A1+A2 and U=A1/G.
Then G~Gamma(2a), U~Beta(a,a), independent. Apply the conditional identity to
G[U/H1+(1-U)/H2]. The standard two-branch beta density calculation gives
4U(1-U)~Beta(a,1/2), independent of the fresh W,G_b and G. Therefore

    Bprime(a,b)+Bprime(a,b)
      =d Bprime(2a,b)*(1+sqrt(Beta(a,1/2)/Beta(b,1/2-b)))

for every a>0, 0<b<1/2, with the source's exact independence convention.

## Counting judgment

This is a short all-parameter bridge from a published product formula for the
literal inverse-Gamma Laplace transform. No unsolved analytic inequality,
strictness upgrade or parameter range remains after substitution. Root
recommends EXCLUSION as a routine classical corollary, even though no earlier
explicit published resolution of the beta-prime conjecture was located. Our
independent ODE proof is a second proof of the same known transform relation,
not a way around subsumption. No Lean or paper investment is authorized by a
novelty conclusion here; all credit stays 0 pending independent adjudication.

## Other bounded checks

* The actual published Ferreira–Simon Conjecture 1 was read in the cached AMS
  full-text HTML from the completed first-campaign Mills final review. It is
  identical to arXiv v2. A fresh AMS viewer request now returns 403; the old
  actual body is retained and hashed, not replaced by its abstract.
* The arXiv v2 PDF printed p.20 was freshly rendered and visually read. Latest
  submission history remains v2 (19 May 2022).
* Bithas et al. arXiv:2610.06073v1 Theorem 1 was actually read: it assumes
  half-integer shapes n+1/2, hence does not cover 0<b<1/2. It is not the exclusion.
* DLMF 10.32.17–18 were actually read and do not by themselves present (D) in
  this form; Durand is the concrete named prior theorem.
* OpenAlex's current source record has 3 indexed citations. This is status only;
  the corpus has not been newly audited in full for Conjecture 1. No absolute
  priority claim, no inference from empty search results and no MathDB status
  change is made.
