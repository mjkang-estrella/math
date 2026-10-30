# r40: full Kurşungöz unimodality question remains unresolved

## Source endpoint and screening

Selected endpoint is the unnumbered Conjecture on p24 of **Palestine Journal of Mathematics 15 (Special Issue III) (2026), 17–24**, published October 1 according to the publisher landing page. It is Conjecture4 of arXiv2502.17117v1 p9. Read the published Theorem1.3 pp23–24 and preprint Theorem3 pp8–9, including initial conditions and ALL nonnegative multiplicity vectors. The published recurrence and conjecture agree. The surrounding partition terminology changes to conventional `(k+1)`-regular; that does not change b or supply a resolution. The conjecture is about coefficients in q of each fixed b, NOT the Bessel-number sequence obtained at q=1.

Other exact accessible questions screened before selection:
* Labelle2502.10655 **latest v4, October19,2026**, Conj7.3 is explicitly restricted to simply laced root systems. The unrestricted older question is already publicly refuted, including the exact polynomial in its own footnote8. Omega's actual Cartan-datum `claim` and `result` body likewise refute the unrestricted assertion using C2 and alpha=(2,2). This is not a fresh route, and it does not refute latest Conj7.3. No endpoint-repair credit.
* Labelle v4 Conj7.2 asks coefficient positivity for all finite types and all nonnegative root-lattice alpha. It is proved in type A in the source. A full finite-type proof would need a positive formula or the degree-controlled regular sequence of Conj7.1; no plausible complete ordinary route emerged here. It was screened out, not silently reduced to A or rank two.

The selected recurrence has a concrete potential full-scope route: induction on total number of blocks, preserving log-concavity and a stronger relation between neighboring predecessor rows. Exact diagnostics below expose why the simplest versions of that route fail. No source counterexample has been found.

## Exact recurrence in consistent coordinates

Our script stores n=(n1,...,nk), reverse of the displayed source ordering. Write N=sum_j j*n_j, A_j(n)=sum_{i>j}(i-j)*n_i, and [t]=1+q+...+q^(t-1). Then

    B(n) = sum_{j:n_j>0} q^A_j(n) * product_{h=2}^j [N-h+1] * B(n-e_j),
    B(0)=1.

Terms with n_j=0 are omitted, so all active q-integers have positive lengths. k=2 gives exactly B(n1=n,n2=m)=[2m+n-1]B(n,m-1)+q^m B(n-1,m).

The constant coefficient is 1: only the largest active j has A_j=0; all other active j have positive shifts. Induction gives the exact degree

    D(n)=sum_j (j(j-1)n_j^2/2-(j-1)n_j)
         +sum_{i>j} j(i-1)n_i*n_j.

Indeed the degree of each nonzero recurrence summand equals D(n): subtracting D(n-e_j) from the formula gives A_j+(j-1)N-(j(j+1)/2-1). This is exactly the degree of the prefactor. This routine degree fact is uncredited.

Iterating the recurrence yields a finite sum over words with letter j appearing n_j times. At each successive remaining vector m, a letter j contributes q^A_j(m) times product_{h=2}^j [N(m)-h+1]. Each word contributes a shifted product of q-integers. Every such individual product is symmetric and log-concave on its support, but the word shifts need not agree. This is an exact positive expansion, not a proof of unimodality of its sum. The independent checker uses ordinary convolution and explicit word enumeration, separate from the main sliding-window recurrence implementation.

## Two exact route falsifiers

1. Common-mode induction on the source recurrence fails already for n=(0,0,1,3), i.e. b(n4=3,n3=1,n2=0,n1=0). The j3 and j4 summands have unique modes38 and37, respectively. Thus even for actual source rows the summands need not have a common mode. Their sum remains unimodal in this example; this is NOT a source counterexample.

2. Log-concavity, positive full support, unit constant term and the correct predecessor degrees do NOT suffice for recurrence preservation, even at k2. At m=2,n=3, take

    f=(1+q)^3,
    g=sum_{i=0}^6 (3/2)^i q^i.

These have the correct predecessor degrees3 and6. Both are log-concave and have constant1. Their recurrence image [6]f+q^2*g has coefficients

    1,4,8,19/2,41/4,91/8,193/16,371/32,793/64.

Its last three coefficients, scaled by64, are772,742,793. The strict down-then-up proves non-unimodality. These f,g are substitute rows, NOT the actual predecessors B(3,1) and B(2,2); the exact source rows satisfy extra relations. This rules out a proposed invariant, not the source claim. An even smaller substitution f=1+q,g=1+(23/10)q+(23/10)^2 q² gives a log-concavity failure for m2,n1, although its sum is still unimodal.

The essential gap is a preserved inequality coupling the actual rows strongly enough to control all coefficient differences (or another full-scope mechanism). Neither positivity, degree agreement, individual log-concavity nor an unproved common-mode assertion closes it. No infinite induction is claimed from finite tests.

## Closest bodies and eligibility limits

* Published primary pp23–24 and arXiv v1 pp8–9 were visually rendered and inspected. Intro/Theorem1 and Lemma2 proof/normalization on pp2–7 were read in extracted text. Published p22's specialization and table are context only; no repaired formula is nominated as a result.
* Author's April10,2025 MTU slides carry the same all-k conjecture (slide17). The institutional bibliography was obtained, but explicitly says updates are temporarily closed; it is incomplete evidence for absence of follow-ups. Public title/author searches found the October2026 journal version, not a full resolution. No exhaustive bibliographic clearance.
* Kurşungöz–Ömrüuzun Seyrek2106.12847 actual Theorem3/Lemma4 p3 and proof setup pp11–13 describe a different positive base-partition expansion, with immobile/movable singletons and pair/block recurrences. Positive coefficients of those generating functions do not imply coefficient unimodality of each normalized B(n). No transport of unimodality was established. The complete published2022 body was not retrieved; this remains a subsumption coverage limit, not a clearance.
* Lewis–Morales2410.19714v3 actual pp1–4, definitions and Propositions1–4 with proofs were read. Their maximal-rank q-rook product argument does give symmetric/log-concave products, but arbitrary q-rook numbers are explicitly non-unimodal. The exact Ferrers-board counterexample is R2(<10,9,3,2,1>), not a Kurşungöz b. No identity embeds that witness in the present family. General q-rook unimodality cannot serve as a bridge; the printed counterexample does not itself refute this source. Publisher DOI10.1080/10586458.2025.2595005 was identified but its typeset body was not read.
* Toda v4 pp20–22 plus intro source statements and actual Omega claim/witness/contradiction bodies were read. The registry's old unrestricted negative endpoint is excluded; it is not evidence for the latest simply laced question or for Kurşungöz.

Current registry screen is in registry-screen.json. Filename/keyword nonmatches are NOT a novelty clearance. No first-resolution or substantive discovery is asserted.

## Capped diagnostics and literal Lean inventory

`bash run-checks.sh` runs serially with hard AS512MiB, finite CPU/wall and BLAS1. Main exact scan checks2538 rows across k2..6 and weighted-size cutoffs32,23,19,17,15. All pass coefficient log-concavity, unimodality and derived degree. Independent expansion checks150 rows /4777 words with <=6 blocks, four possible block sizes and multiplicities<=3. It also reproduces the two route falsifiers. These finite positive checks have no universal logical force.

No Lean declarations, files or compilation were attempted. A literal source endpoint would be `forall k>=2, forall n : Fin k -> Nat, Unimodal (B k n)` with an explicitly defined polynomial recurrence and source coordinate identification. Missing bridges: the full coefficient-shape theorem for that recurrence and its all-k induction invariant. Helpers or the finite route obstructions do not justify formal investment. No PROOF.md because there is no full proof or refutation.

Credit0; counts unchanged5additional/35total. Root alone owns acceptance. All writes confined to assigned r40; solo, no git, children, browser tabs, contact, posts, uploads, accounts or other-lane edits.
