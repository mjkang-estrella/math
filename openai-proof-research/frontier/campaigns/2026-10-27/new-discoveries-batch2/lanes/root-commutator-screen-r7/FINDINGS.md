# Root research checkpoint — 2026-10-28 — no outcome nominated

This lane adds exact strategy exclusions and two source leads. Credit is zero.
No full ordinary theorem, literal Lean endpoint, manuscript or acceptance is
claimed. The three live Pi tasks were neither polled nor disturbed.

## 1. Weighted commutator: a proposed sufficient estimate is false

The actual arXiv:2403.04199v2 Conjecture 1, equations (14)–(16), was read.
The general weighted Frobenius problem remains unsolved here. The completed
pi-matrix-discovery-r3 lane's change of variables gives the core target

    ||X W Y - Y W X||_F^2 <= (w1^2+w2^2) ||X||_F^2 ||Y||_F^2,

where W is positive with descending eigenvalues w1,w2,... . This is not a
new reduction or result credited to this lane.

A new attempted route decomposed a two-level W as bQ+(a-b)P with P<=Q
orthogonal projections and rank(P)=1. Writing C_T=XTY-YTX, the estimates

    ||C_Q||^2 <= 2 ||X||^2||Y||^2,
    ||C_P||^2 <= ||X||^2||Y||^2,
    Re <C_Q,C_P> <= ||X||^2||Y||^2

would yield the sharp a^2+b^2 bound by expansion. The THIRD estimate is false,
already for Q=I_2, P=diag(1,0), X=diag(2,-1), Y=E12:

    C_Q=3E12, C_P=2E12, Re<C_Q,C_P>=6,
    ||X||^2||Y||^2=5.

This is an exact counterexample to the proposed helper, NOT to the source
conjecture. Indeed W=diag(2,1) gives ||C_W||^2=25=(4+1)*5, exact equality
in the actual conjectured bound. More generally the remaining source gap for
this same pair is the nonnegative square

    5(a^2+b^2)-(2a+b)^2=(a-2b)^2.

The false mixed estimate must not be used in any future formal proof.
check_exact.py verifies every matrix computation with rational arithmetic.
The exploratory float optimizer suggested the larger mixed constant
(1+sqrt(2))/2, but no general assertion about that constant is made.
No numerical optimizer state is needed or relied on by the exact obstruction.

## 2. Nearby q-commutator conjectures are publicly refuted

The actual arXiv:2202.11520v2 Section 3 states two conjectures with the
DISJUNCTION that either matrix is traceless. Both already have public literal
Lean refutations in trureturing, inspected read-only at immutable clone HEAD
f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada:

- Blueprint/D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.md:
  n=3, q=-1, A=diag(2,-1,-1), B=diag(1,0,0), source coefficient 2,
  exact left mass 16 > right mass 12.
- Blueprint/D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.md:
  n=5, q=2, A=[[6,42],[0,-3]] direct-sum -I3,
  B=[[6,0],[-42,-3]] direct-sum -I3. Both traces vanish. Exact masses
  ||A||^2=||B||^2=1812 and left mass 16417164 > 16416720, gap 444.

These prior examples were independently recomputed here using exact matrices
in check_exact.py. They exclude rediscovery credit for the same refutations;
no upstream Lean replay or authorship is claimed. The immutable public files
are at https://raw.githubusercontent.com/the-omega-institute/trureturing/
f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada/Blueprint/D5/S3/QuantumBounds/
followed by the respective filename. A registry's silence elsewhere would not
undo this public prior art.

## 3. Distinct mixed-inner-product question: open lead, no proof

Chruscinski–Kimura–Ohno–Singal, arXiv:2208.10005v1, Theorem 1 and the
conjecture immediately after it (LAA 656 (2023),158–166,
doi:10.1016/j.laa.2022.09.022) ask for all complex square matrices the sharp
bound on Re<[X,Y],[X,Y]_q> with

    c(q)=(1+q+sqrt(2(1+q^2)))/2, q real.

They prove it for n=2 and whenever one matrix is normal. This is a DIFFERENT
quantity from ||XY-qYX||^2 and the public refutations in section 2 do not
refute it. The actual v1 HTML theorem, definition and neighboring conjecture
were read, rather than relying on the abstract. No MathDB identifier has been
verified for this lead, and no full novelty clearance is claimed.

An unproved sufficient joint-range assertion could be a useful next attack.
For ||X||=||Y||=1 set u=||XY||^2, v=||YX||^2,
z=Re<XY,YX>, r=u+v-2z, d=u-v. Then the exact identity is

    Re<[X,Y],[X,Y]_q> = ((1+q)r+(1-q)d)/2.

If one could prove (r-1)^2+d^2<=1 for arbitrary X,Y, scalar Cauchy–Schwarz
would imply the source bound c(q). This CIRCLE ASSERTION IS UNPROVED HERE;
it must not be confused with a proven classical matrix theorem. For normal
X=diag(a,b,0,...) and Y=E12, a,b real with a^2+b^2=1, one obtains
(r-1,d)=(-2ab,a^2-b^2), so every point of the unit circle occurs already
in the known normal case. This explains the sharpness geometrically but
earns no credit. The formal algebraic decomposition alone is checked in
check_exact.py. No equivalence stronger than the stated sufficiency is claimed.

Nobori, arXiv:2608.03897v1, published online August 2026 as LAA 751,
183–195, doi:10.1016/j.laa.2026.08.001, gives other upper bounds on the
SQUARED q-commutator norm. Actual Theorem 1.1 and Section 3 were read.
Its Proposition 3.1 is a nonsharp-interior two-dimensional polynomial upper
bound, not a resolution of the mixed-inner-product question above. The
paper explicitly leaves the all-q sharp norm constant undetermined. No
published-body comparison of either new matrix lead was completed here.

## 4. Game of Cycles: preserve genuinely open targets

Actual BBFS arXiv:2208.05147v2 Section 7 lists remaining theta families,
including middle-path length 3 and short odd paths. Corollary 7.1 covers
middle-path length 2, not all embeddings merely because a path has length 2.
The paper's chordless-cycle gloss and embedding-dependent bounded cells must
be reconciled faithfully before a source-level theorem is posed. The old
pi-combinatorics lane's finite parity census and chordless-gloss witness are
not promoted or recounted. No general theta strategy was found here.

The newer actual primary arXiv:2610.15145v1 (Muchen Xu, 10 October 2026)
already proves the tempting spider results and blocked/free path Nim model:
Theorem 9.1 gives a binary-carry formula for S(1,2j,z), and the other theorem
families cover S(2,3,z), eventual parity for 99 fixed pairs, and short threads.
They are public prior art, not future discovery candidates. The formula in
Theorem 9.1 only takes values 0 and 1 and cannot by itself prove unbounded
tree Grundy values.

Actual Section 11 leaves: Conjecture 11.1 (every nonnegative tree Grundy
value); Question 11.4 (internal threads<=2 and leaf threads<=3 parity);
Question 11.6 (Grundy values on 2-connected plane graphs). Proposition 11.2
already proves unbounded values for BLOCKED, status-labelled positions;
that does not realize them on empty unmarked trees and is not a solution
of Conjecture 11.1. No new proof or refutation is claimed for any of these.

## Accounting and next action

Credit 0, additional accepted 0/30, previous first thirty untouched.
This checkpoint prevents three false promotions: the failed mixed estimate,
already posted q-commutator refutations, and already proved 2026 spider facts.
The mixed-inner-product joint-range route and the precise game questions are
available for future mathematical work; neither warrants full formalization
without a complete proof. All six primary HTML sources and their retrieval
hashes are preserved. Source/journal-access and global-novelty limits remain.
