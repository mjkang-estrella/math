# RSK non-integer spectrum: unresolved full question, exact route obstruction

Research performed 2026-10-29 UTC (2026-10-28 America/Los_Angeles).
Solo assigned lane; no acceptance authority. No discovery nominated; credit 0.
Campaign counts remain 3/30 additional, 33/60 total. No PROOF.md or Lean work.

## Source selection and full scope

Target: Ada Stelzer and Alexander Yong, *RSK as a linear operator*,
arXiv:2410.23009v1 (October 30, 2024), Conjecture 5.8; retained as
Conjecture 5.8 in Selecta Mathematica 32, article 88 (2026),
https://doi.org/10.1007/s00029-026-01191-5 . The actual publisher body reports
received December 1, 2024, accepted March 27, 2026, published August 24, 2026.
Actual Definitions 1.7, 4.4, Sections 2.1–2.3, Proposition 5.3,
Conjectures 5.5 and 5.8, Remark 5.9 and surrounding proofs were compared,
not just indexed labels. The publisher and original bodies were retrieved
successfully at 05:03 UTC. No assertion that arXiv v1 is its latest revision.

For every pair of positive compositions sigma, pi of the same integer d,
with m=len(sigma)<=n=len(pi) and the source's lexicographic normalization
when m=n, form the finite contingency-table space with those margins.
The operator T sends each monomial z^alpha to the product of minors [P|Q]
where (P,Q)=RSK(alpha), extended linearly over C. Reduced means

    max(sigma)+max(pi)<=d.

A reduced pair is triangular exactly when m=2 and sigma_1=pi_1.
The question is whether EVERY reduced non-triangular pair has an eigenvalue
outside Z. The full unrestricted question is the objective here; the
calculable two-row subproblem is not substituted as a completed outcome.
MathDB365595 identifies this claim, but its indexed open label supplies no
novelty evidence. Zero-entry/empty-weight domain objections were not pursued.

Before selection, read both governing AGENTS.md files, ledger.json, NEXT.md,
prior-campaign-context.json, the named discrete-r6/denominator-r1/matrix-r6
summaries, discrete-r6's discovery history, astra-discrete-r3's actual argument and
its routine-corollary objection, the old twenty-proof-discrete-lane report,
and the discrete frontier scout. This reconciles all first33 and named
exclusions. The prior fresh-discrete lane had only screened the RSK source;
it did not attack or resolve this question. No excluded family was reused.
Chronology limitation: the full denominator-r1 and matrix-r6 discovery
histories were read after the spectral attack; their summaries were read
before selection. They reinforce their exclusions and do not address this
RSK target. The initial combined ledger output was truncated; a later
structured compact read supplied its candidate/exclusion entries.

## Early source-level public exclusions and bounded registry coverage

1. Duy Phan–David Xia, https://arxiv.org/html/2504.05510v1 (April 7, 2025),
   Theorems 1.2–1.3 and Corollary 2.6, explicitly prove the zero-diagonal
   density Conjecture 8.7. Read the actual theorem statements and insertion/
   lateral-bump bridge. It is a different quantified statement, not 5.8.
   No work on zero density is credited or proposed.
2. Bohao Zhang, *Representation theory of general linear groups and RSK as
   a linear operator*, https://zenodo.org/records/23655610 (October 26, 2026).
   Read the entire six-page actual PDF. Theorem 1.1 and Proposition 4.1
   identify RSK_((2n-2,2),(2^n)) with Sym^2 of an n-cycle, and give its
   characteristic/minimal polynomials. Those special weights and spectral
   formulas are already public and receive zero credit. This is not the
   arbitrary-margin claim. Its proof is not presumed valid merely from the
   abstract; the explicit four-case insertion calculation was read and its
   low members independently checked here.
3. Reused the complete recent cache and actual HEAD receipts in
   sol-fresh-analysis-discovery-r7, as instructed. Omega HEAD
   67b4fae085cf19003a33f8027410c383b49e5046, commit 2026-10-29T04:37:11Z,
   receipt 04:39:40 UTC; complete Problems and D5 trees fetched 04:39:41–42.
   OpenAI HEAD 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; count-ex-machina
   HEAD dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. The complete tree path
   screens and count registry had no matching claim. Read the actual pinned
   RSKMinimalInversionHankelRefutation.lean hit: its claim concerns minimum
   inversion matrices of RSK shape (8,8,1,1) being Hankel. It neither defines
   nor proves the present spectral assertion. Substring false hits such as
   Stolarsky/KnasterTarski are preserved in registry-screen.json.

No GitHub API requests or broad traversals were performed. The prior GitHub
API rate limit and direct MathDB403 were respected by making no requests to
those affected hosts. All requests here succeeded; no host was challenged or
retried. No later HEAD refresh is claimed. Tree completeness is not full-text
coverage or proof of absence of a subsumer. Public exact-title, source-name,
and eigenvalue-phrase searches found the above bodies but did not provide
acceptance-grade worldwide novelty clearance. No priority claim is made.

## Exact general two-row coefficient reduction

For arbitrary n and margins sigma=(s,d-s), pi=(p_1,...,p_n), write an input
monomial as product_j x_j^(a_j) y_j^(p_j-a_j), where sum a_j=s.
The source reads biletters down columns from left to right. Set B_0=0 and

    c_j=min(a_j,B_(j-1)),
    B_j=B_(j-1)-c_j+p_j-a_j,
    C=sum_j c_j.

Then P has rows 1^s 2^(B_n) and 2^C. Q has first row consisting of j repeated
p_j-c_j times in sorted order, and second row of j repeated c_j times.

Proof: before column j, P's first row consists of all its accumulated ones
then B_(j-1) twos. Inserting a_j ones replaces precisely min(a_j,B_(j-1))
of those twos, bumping each to row two. Since row two consists of twos,
these simply append there. The remaining ones append in the first row.
The subsequent p_j-a_j twos all append in row one. The new row-two boxes
record j; the remaining new boxes record j in row one. Induction proves
all formulas, including C+B_n=d-s. This is an elementary coefficient
construction, not a new result claimed for credit.

Let u_1,...,u_(d-C) be the first-row Q word and v_1,...,v_C the second.
The resulting image polynomial is literally

    product_(k=1)^C (x_(u_k)y_(v_k)-x_(v_k)y_(u_k))
    * product_(k=C+1)^s x_(u_k)
    * product_(k=s+1)^(d-C) y_(u_k).

Semistandardness gives u_k<v_k. Thus no numerical RSK or eigenvalue
approximation is needed. A sparse integer product computes every coefficient.
For n=3 the number of monomials is O(d^2); the diagnostics cap degree,
dimension, memory and CPU explicitly. General n is not enumerated.
The direct row-insertion implementation and independent greedy formulas
agree throughout all computed two-row inputs.

## Ordinary spectral reduction and attacks

The source Proposition 2.7 makes A an integer unimodular matrix. Its monic
characteristic polynomial has constant term +/-1. The rational root theorem
therefore restricts rational eigenvalues to +/-1 (Proposition 5.3).
Writing N=dim A, the following are equivalent over characteristic zero:

- all eigenvalues are integers;
- all eigenvalues are +/-1;
- (A^2-I)^N=0;
- tr(A^(2k))=N for every 1<=k<=N.

For the third equivalence use the characteristic polynomial and
Cayley–Hamilton, or Jordan form. For the last, apply Newton identities to
A^2: its first N power sums equal the power sums of N copies of 1, so its
characteristic polynomial is (t-1)^N. Conversely eigenvalues give the traces,
including in the presence of Jordan blocks. This reduction is classical and
is not a discovery. Showing A^2!=I alone is INSUFFICIENT: nontrivial Jordan
blocks may have only the eigenvalue 1.

### Second moment criterion: false on the actual source family

The attractive stronger invariant was tr(A^2)!=N at every non-triangular pair.
It holds in all the initial degree<=8 two-row diagnostics but is false.
For sigma=(5,5), pi=(4,4,2), N=13, the exact matrix has

    tr(A^2)=13,    tr(A^4)=85,
    char_A(t)=(t-1)^3(t+1)^2(t^3+3t^2-1)
              *(t^5+t^4+t^3+2t^2-t-1).

The pair is genuinely interior: max sigma+max pi=9<10, with sigma_1!=pi_1.
Thus this is an obstruction within the intended domain, not a boundary or
wording correction. route-checks.json retains the entire matrix and basis;
route_check.py recomputes all entries, the polynomial factorization and traces
using exact arithmetic. This is NOT a counterexample to 5.8: it has
non-integer eigenvalues. Two later moment-blind examples are retained in
moment-probe.json; no moment-blindness is mistaken for an integer spectrum.

There is also no uniform sign for N-tr(A^2): the source's golden-ratio pair
(22,121) has N=4,tr(A^2)=5, whereas (21,111) has N=3,tr(A^2)=0.
A positivity proof must distinguish different spectral mechanisms.

### Small-cycle block inheritance: false shortcut

The known (21,111) block has characteristic polynomial t^3-1. But the
non-triangular (22,121) block has (t-1)(t+1)(t^2-t-1), which has no primitive
cube root. Thus every non-triangular pair cannot contain the same known
three-cycle spectral block. The ambient degree-space block decomposition
does not imply that an individual arbitrary margin block contains it.

Multiplication embeddings also fail outside the source's exact commuting
hypotheses. Let alpha=[[0,1,1],[1,1,0]] at margins (22,121). Direct expansion gives

    T(z_11*z^alpha)-z_11*T(z^alpha)
      = x_3*(x_2*y_1-x_1*y_2)^2 != 0,

where x_j=z_(1j),y_j=z_(2j). route_check.py checks this exact polynomial.
Here sigma_1+pi_1=3<d=4, so Theorem 1.5 deliberately does not authorize the
embedding. Any argument transferring known eigenvalues into arbitrary
reduced blocks must supply a different invariant subspace or quotient.

### Modulo-two route: promising but unproved

If all integer eigenvalues are +/-1, then modulo 2 the characteristic
polynomial is (t+1)^N. Necessarily (A+I)^(2^ceil(log2 N))=0 over F_2.
The converse is not asserted: a polynomial can split this way modulo 2
without having only +/-1 roots in characteristic zero.

Bitset exact matrix squaring tests this necessary condition without any
floating eigenvalue calculation. All 1,678 positive reduced non-triangular
2x3 pairs of degree3..24 fail it. All 206 normalized positive reduced 3x3
pairs of degree3..8 fail it too. The latter implementation directly expands
minors of sizes <=3 and is separately cross-checked against source Table5;
the former is cross-checked against Table6 and triangular involutions.
These finite certificates provide no full theorem or fixed-range credit.

The exact missing step is a uniform proof, for EVERY reduced non-triangular
pair, that A modulo 2 has a non-unipotent factor, or another source-wide
argument ruling out nilpotence of A^2-I over Q. No such structural result
is established. It may even be false outside the tested margins. The
2-row greedy formula alone controls coefficients, not characteristic factors;
for m>=3 it does not describe insertion. A source-wide proof must handle
arbitrary lengths and degrees. A certified small-range extension cannot fill
these gaps. No known-hard famous reformulation is being claimed as progress.

## Validation, limits, and literal Lean prospect

Run, in order, from this lane (Python3, SymPy1.14):

    python check.py
    python moment_probe.py
    python spectral_probe.py
    python general_check.py
    python route_check.py

Each imports check.py first, which hard-caps address space at512MiB and CPU
at120seconds and sets BLAS/OpenMP/MKL/NumExpr threads to1 before any SymPy.
All searches have finite parameter ranges, dimensions<=100 and no recursive
unbounded/exponential search. Two-row table enumeration is polynomial for
fixed three columns; the extra known-family checks use at most six columns
of fixed margin2. Three-row enumeration is restricted to3x3 degree<=8,
polynomial in d for that fixed shape. There are no random or numerical tests.
Diagnostics are not a proof of the source statement. Formal proof tokens in
external registry files are not trusted or imported as new certificates.

A plausible literal Lean route would define contingency tables as a Finset,
RSK insertion on lists, determinant products as MvPolynomial Z, then the
coefficient matrix. The greedy formula offers an induction endpoint only
for two rows. The algebraic nilpotence/mod2 implications are standard finite
matrix facts. The unproved arbitrary-margin structural statement remains the
main bridge; encoding it as an assumption would not prove the source claim.
Therefore no major Lean work, paper, complete ordinary candidate, PROOF.md,
or formal endpoint was started. If justified later, only pinned4.34.1 /
mathlib d13f23b with the standard three axioms and serial <=3GiB RSS applies.

Strongest objection: there is no complete ordinary proof or source
counterexample, and no acceptance-grade novelty investigation. The retained
contribution is a reproducible source-level reduction and exact failed-route
record. It earns zero credit, including its helpers and finite checks.
