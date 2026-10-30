# Research disposition: full source question remains unresolved

No qualifying discovery, acceptance recommendation, or Lean endpoint. Credit 0.
The mathematical work below is partial and explicitly excluded from the campaign count.

## Primary target and literal quantifiers

Ludovick Bouthat, *On the monotonicity of left and right Riemann sums*,
arXiv:2311.01208v2 (16 February 2024), Section 3.1, Conjecture 3.2, PDF p18.
Published version: Sampling Theory, Signal Processing, and Data Analysis 22,
article 14 (9 May 2024), DOI 10.1007/s43670-024-00088-8.
Both complete HTML bodies were retrieved and their Conjecture 3.2 and concluding
question (3) read. The published body still asks whether Conjecture 3.2 can be
proved or disproved; this is stronger source evidence than a database open label.

For b<2 let f_b(x)=1/(1-bx+x²), 0≤x≤1, and, for every integer n≥1,
L_n=(1/n) sum_{k=0}^{n-1} f_b(k/n), R_n=(1/n) sum_{k=1}^n f_b(k/n).
Set β+=(3+sqrt(13))/4. Conjecture 3.2 consists of ALL of:

* For each b in (1/2,1), the sequence L_n is neither increasing nor decreasing.
* For each b in (β+,2], L_{n+1}≥L_n for every n≥1.
* For each b in (1,3/2), R_n is neither increasing nor decreasing.
* For each b in (β+,2), R_{n+1}≤R_n for every n≥1.

The b=2 left endpoint is meaningful as a finite sum excluding x=1 and is
already treated by source Remark 3.3. It is NOT a new result. Theorem 3.1
already covers L increasing on [1,β+] and R decreasing on [3/2,β+].

Exact MathDB record: 360607,
https://mathdb.com/p/360607/conjecture-on-the-monotonicity-of-riemann-sums-for-reciproca .
The public search/fetch tool read its actual statement on 2026-10-29 UTC,
including zero solutions. Its sentence that remaining assertions are addressed
by subsequent results must not be used as evidence of a resolution: the actual
published conclusion explicitly retains Conjecture 3.2 as an open question.
Direct HTTP MathDB access returned 403; no retry/challenge bypass was attempted.
The text read by the web tool is retained in sources/mathdb-readback.txt, with
its hash and retrieval channel in provenance.json; it is a transcription, not
raw origin-response bytes.

## Live prior-proof and source investigation

Fresh public heads, retrieved 2026-10-29T04:39 UTC, BEFORE derivation:

* the-omega-institute/trureturing 67b4fae085cf19003a33f8027410c383b49e5046,
  head commit 2026-10-29T04:37:11Z; D5 and Problems subtree listings complete.
* suvrit/count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a,
  head commit 2026-09-09T15:24:07Z; current registry (19 entries) read/searched.
* openai/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
  head commit 2026-10-26T21:18:03Z; complete preprints subtree and current CONTENTS.

Screened bouthat/riemann-sum/Borwein/source-ID terms. Two omega Bouthat hits
were actually downloaded and body-read: they concern path complete homogeneous
symmetric graph norms in arXiv:2606.17356 Remark 4.3, not Riemann sums, and do
not assert this target. Count registry has no target hit. No target manuscript
was identified in current OpenAI preprint paths or catalogue. The ancestor
immutable catalogue/upstream metadata were also consulted. No reliance on the
wrong teorth repository. These targeted screens are NOT a full-text search of
every proof in every repository. General quadrature theorem subsumption remains
possible; no universal novelty certification.

Public search for source-ID and Bouthat/Riemann-sum conjecture combinations
found the source and earlier Borwein–Borwein–Sims/Bouthat–Mashreghi–Morneau-Guérin
work discussed in the actual source Sections 1.2–1.3. The source explicitly
corrects earlier mistaken proofs. No new general theorem was inferred from
search abstracts. The actual 2024 publisher HTML is readable; there is no
unread-publisher-source HOLD for this target's statement. Earlier papers were
not fully body-compared independently: this remains a prior-art limitation.

Read both requested r5/r6 summaries and current ledger/NEXT/prior context.
Excluded all explicitly forbidden families. This is a distinct source question.
Campaign counts remain 3/30 additional, 33/60 total. No shared edits.

## Actual mathematical work

### 1. Elementary nonmonotonicity bridge: complete but routine, no credit

Direct substitution gives

  L_2-L_1 = (2b-1)/(2(5-2b)),
  R_2-R_1 = (3-2b)/(2(5-2b)(2-b)).

Both are strictly positive on the corresponding nonmonotonicity ranges.
For each fixed b<2, f_b is smooth on [0,1]. Classical Euler–Maclaurin gives

  L_n = I+(f_b(0)-f_b(1))/(2n)+(f_b'(1)-f_b'(0))/(12n²)+O_b(n^-4),
  R_n = I+(f_b(1)-f_b(0))/(2n)+(f_b'(1)-f_b'(0))/(12n²)+O_b(n^-4).

Subtracting adjacent terms is legitimate with the displayed O(n^-4) remainder:
if the coefficient of 1/n is A>0, the difference equals -A/n²+O_b(n^-3),
hence is negative eventually. Here f_b(0)=1 and f_b(1)=1/(2-b).
For 1/2<b<1, the L coefficient is positive; for 1<b<3/2, the R coefficient
is positive. Thus both source nonmonotonicity clauses follow. This is an
explicit classical bridge and is EXCLUDED as a routine corollary and as only
part of the full conjecture. No PROOF.md or formalization investment for it.
The constants depend on b, so this does not give the missing uniform range.

### 2. Exact mesh/parameter representation and a genuine remaining gap

Write ε=2-b>0 and reverse the grid index j=n-k. Then EXACTLY

  S_n(ε)=sum_{j=1}^{n-1} n/[j²+ε n(n-j)],
  L_n=S_n+1/n,    R_n=S_n+1/(ε n).

For fixed j and real x≥n≥j+1 define
  a_j(x)=x/[j²+ε x(x-j)].
Direct quotient differentiation yields
  a_j'(x)=(j²-ε x²)/[j²+ε x(x-j)]².

Consequently
  S_{n+1}-S_n = (n+1)/[n²+ε(n+1)]
                  +sum_{j=1}^{n-1} integral_n^{n+1} a_j'(x) dx.          (1)
This includes n=1 with the empty sum. The j=n boundary term is essential.

For x≥n and j<n the denominator is at least j², so a_j'(x)≤1/j²
(whether its numerator is positive or negative). Also sum_{j=1}^{n-1}1/j²<2:
for j≥2 use 1/j²≤1/[j(j-1)] and telescope. The boundary term is ≤2/n.
Thus, rigorously,

  R_n-R_{n+1} ≥ 1/[ε n(n+1)]-2-2/n.

In particular it is strictly positive if ε(n+1)²<1/2.
In this same regime a_j'(x)≥0, since εx²<1/2≤j²; (1) then gives
  L_{n+1}-L_n ≥ (n+1)/[n²+ε(n+1)] -1/[n(n+1)] >0.
For the final inequality ε<1 suffices: cross multiplication leaves
n(n+1)²-n²-ε(n+1)>0, bounded below by n³+n²-1>0.

These are rigorous subrange signs, NOT the source's all-n theorem.
For any fixed ε>0 this low-mesh range is finite. It does not settle the
transition n sqrt(ε)≈1 or arbitrary larger n uniformly as ε→0.
The exact checks at ε=1/[4(n+1)²], n=1..30 independently validate the formulas
and bound, but do not replace the inequalities proved here.

### 3. Rational numerator cone attack

R_n(b)=sum_{k=1}^n (1/k)/(k/n+n/k-b).
All poles are real ≥2. For each fixed n clear denominators in R_n-R_{n+1};
orient the denominator positive at b=1 (all factors have constant sign for
b<2). Let N_n be the resulting numerator with degree d. Substitute
b=(3+4t)/(2+2t), mapping t≥0 onto [3/2,2), and multiply N_n by [2(1+t)]^d.
Every resulting coefficient is nonnegative for n=1..12 (exact integer
arithmetic). This certifies those finite n over the ENTIRE parameter interval,
not merely pointwise numerical tests. At n=1 the constant coefficient is zero.
No all-n coefficient formula or inductive invariant has been proved.

An expanded geometric route writes
  f_b(x)=sum_{m≥0}(b-1)^m h_m(x),
  h_m(x)=x^m/(1-x+x²)^(m+1).
For 1≤b<2 convergence is uniform because 0≤x/(1-x+x²)≤1 and b-1<1.
Diagnostics for m=1..60,n≤120 found L_n(h_m) increasing and R_n(h_m)
decreasing. However m=0 has R_n(h_0) INCREASING by the source's b=1 theorem.
Thus even an all-m proof of the observed m≥1 signs does not imply the desired
right-sum sign: a quantitative domination of the m=0 increment is still needed.
Treating it as a termwise positive expansion would be a logical error.

### 4. Exact falsifiers for tempting proof shortcuts

The pole representation does not give ordinary first-order stochastic order.
If μ_n= sum_{k=1}^n (1/k) δ_{k/n+n/k}, then its lower-tail mass at cutoff
r+1/r, 0<r≤1, equals sum_{k/n≥r}1/k. For n=2 versus n=3:

* r=3/5 gives μ_2 tail minus μ_3 tail = -1/3;
* r=7/10 gives the same difference = +1/6.

So their cumulative difference changes sign. A positive-kernel argument using
an everywhere nonnegative cumulative signed measure is false already here.

Nor are all adjacent-difference numerator roots real. At n=2 the numerator is,
up to nonzero scaling,
  72b³-378b²+655b-370,
whose discriminant is -2755260<0. It has a nonreal conjugate pair. Therefore
no real-root interlacing proof for these numerator polynomials can be assumed.
The discriminant and both CDF differences are checked exactly in identities.py.

## Strongest objection/falsifier and endpoint status

There is no proof that ALL N_n transformed coefficients are nonnegative.
A single n with a negative coefficient would refute that sufficient strategy
(though not necessarily the conjecture); a single b in (β+,2), n≥1 with
L_{n+1}<L_n or R_{n+1}>R_n refutes a substantive source clause. No such witness
was found in the bounded checks. The finite-n cone pattern and low-mesh bound
leave an actual infinite quantifier gap, not a source-normalization nuisance.

The full Conjecture 3.2 is unresolved in this lane. No theorem nomination,
PROOF.md, Lean stub, acceptance judgment, priority claim, or count increment.
If revisited, first refresh live registries again. A formalization plan is
premature until an all-n ordinary argument exists. Were such an argument found,
it must connect literal finite rational sums, both monotonic sequences and the
classical asymptotic sign clauses; numerical signs alone are insufficient.
