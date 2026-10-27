# Prospective refutation of the squared Pólya–Szegö clause

Status: complete mathematical construction and CLOSED Lean first-clause counterexample; **credit 0**.
Fresh isolated strict replay PASS100/9; parent read all100 types/axioms; only standard3.
Two-page draft rendered and read. Independent review, novelty clearance, final packet and extracted replay remain pending.
The separate Diaz–Metcalf clause has older claimed negative examples, but the
closest examples fail verification at their stated bounds (see correction below).
It is retained as uncredited supplementary mathematics pending a full prior-art decision. A single possible future credit concerns the first clause only, conditional
on serious prior-art comparison and the full campaign gates.

## Exact source

Moslehian–Fu, arXiv:1501.02939v1, Conjecture 2.16 on printed p.9.
The actual PDF was downloaded and this page rendered and visually read. Its first
coefficient is **one quarter times the square of the sum**, matching MathDB 329636.
The arXiv history has v1 only. The published reference is LAA491 (2016),73–82,
DOI10.1016/j.laa.2015.01.041. The correct ScienceDirect PII is S0024379515001160;
the published body remains access-blocked. A first attempted PII ending 0564 was
wrong and is not evidence about the source. The fresh MathDB snapshot is open with
all activity arrays empty; that is not novelty evidence.

The source inequality is

    (Phi(U)#Phi(V))^2 <= alpha^2 Phi(U#V)^2,
    alpha = (sqrt(M1 M2/(m1 m2)) + sqrt(m1 m2/(M1 M2)))/2,

for unital positive linear Phi and m1² I <= U <= M1² I,
m2² I <= V <= M2² I. Here # is the usual operator geometric mean.

## Construction and proof

Let I be the 2×2 identity and set

    P = [[1,-1],[-1,1]]/2, Q = diag(1,0), t=32, h=t²=1024,
    A = I+(h-1)P, B = I+(h-1)Q,
    U = diag(A,B), V = diag(B,I).

P,Q are orthogonal projections. Thus both U,V have spectra in [1,1024]. Take
m1=m2=1, M1=M2=32, so alpha=1025/64. Define Phi on the whole complex matrix
algebra M4(C) by Phi(Z)=(Z11+Z22)/2, with 2×2 diagonal blocks. It is complex-linear,
unital and completely positive: it is the sum of the two compression maps scaled
by 1/2. Off-diagonal blocks of Z are simply discarded. The example therefore uses
an honest map on the full algebra, not only its block-diagonal subalgebra.

Write

    F=(A+B)/2, G=(B+I)/2, T=diag(32,1),
    s²=1054721/2048, d²=4100/1054721,
    s>0, d>0, r=tr(F^-1 G).

Since det A=det B=h, direct exact multiplication gives

    (A+B) A^-1 (A+B) = s² B.

Both (A+B)/s and A#B are positive definite solutions of X A^-1 X=B. This
solution is unique: conjugate by A^-1/2 and use uniqueness of the positive square
root. Therefore A#B=(A+B)/s. Since B#I=T, block functional calculus yields

    C := Phi(U#V) = F/s+T/2.

The same Riccati characterization gives the explicit output geometric mean

    D := F#G = (G+d F)/sqrt(r+2d).

Indeed d²=det G/det F, and the two-dimensional Cayley–Hamilton identity, or direct
matrix multiplication, gives

    (G+d F) F^-1 (G+d F) = (r+2d)G.

All factors used for positivity are strictly positive. No indefinite square root
or merely entrywise square root occurs.

For v=(1,2), evaluate vᵀ(alpha² C²-D²)v. If a=1/s=sqrt(2048/1054721), b=d,
the expression is exactly

    alpha² [a² vᵀF²v + (a/2) vᵀ(FT+TF)v + vᵀT²v/4]
       - [vᵀG²v + b vᵀ(GF+FG)v + b² vᵀF²v]/(r+2b).

The script check_exact_witnesses.py proves all displayed matrix identities by
exact rational symbolic arithmetic. It encloses each of a,b in adjacent rational
multiples of 10^-12, verifying the bounds by squaring. Outward rational interval
arithmetic on the last expression gives an upper bound strictly below **−17000**.
All divisions have positive interval denominators. The full exact bounds are in
exact-witnesses.json. Thus alpha² C²-D² is not positive semidefinite, refuting the
first clause with strictly positive inputs.

If an endomorphism M4(C)->M4(C) is preferred, replace Phi by diag(Phi,Phi).
Every output and its geometric mean is doubled block diagonally, and use (v,0).
This meets even that narrower reading of the source's map convention.

## Non-isolated mechanism (not separate credit)

Use the same construction with variable t>1, h=t². Let F0=(P+Q)/2 and Q as above.
Then F/t² -> F0, G/t² -> Q/2, and

    C/t -> C0=(P+Q)/sqrt(2)+Q/2,
    D/t² -> Q/2.

The second limit follows directly from the displayed 2×2 formula, since
d=O(1/t), tr(F^-1 G)->1. For v=(1,2),

    lim t^-4 vᵀ(alpha² C²-D²)v = (sqrt(2)-2)/16 < 0.

Hence all sufficiently large t also violate the proposed bound. This uses no
numerical conjecture, though only the explicit t=32 witness is proposed for Lean.
The implied norm-ratio limit is 4−2sqrt(2)>1 (not an optimal-constant claim).

## Separate rational Diaz–Metcalf witness — uncredited

For t=16 set A2=[[257,255],[255,257]]/2, B2=diag(256,1). Take U2=diag(I,A2),
V2=diag(B2,A2) and the same Phi. Then C2=Phi(U2#V2)=[[289,255],[255,259]]/4,
M2=(Phi(U2)+Phi(V2))/2=[[514,255],[255,259]]/4.
With v2=(19,-20),

    v2ᵀ[(257/32)² C2²-M2²]v2 = −2449502775/8192.

This is an exact supplementary witness, with no separate credit proposed.
Hoa–Binh–Ho2015/2017 Remark1 CLAIMS a negative example for K(h)(X#Y)² >= (X∇Y)²,
a special case of this clause. But its stated m=.02,M=11 gives K=303601/2200,
and our exact re-evaluation makes the difference POSITIVE DEFINITE: its leading
minor is 910803sqrt(6)/8000+95141243/198000, and determinant is
88033691903/87120000+10018833sqrt(6)/12800 > 0, not the printed −4.1122.
See check_prior_diaz.py and prior-diaz-correction.json. The 2016 follow-up gives
other matrices whose diagonal entries already violate its stated m=1 lower
bound. Thus neither example may be treated as a verified previous refutation.
The earlier parent description of the second clause as already resolved was
withdrawn after this check. Other prior claims and possible valid examples still
require a serious independent comparison; no novelty PASS is inferred.

## Unfinished gates and limits

The first clause has not yet received an independent subsumption/novelty review.
The initial registry scan at immutable trureturing f8ffe9ed... had no source ID,
title or author match for this problem; it did find the already-known Wielandt
refutation 324727, which is rejected separately. A scan is not a priority certificate.
The six OpenAlex citing records are saved, but their bodies are not all cleared.
The published LAA source body, More accurate operator means inequalities (2018),
and the 2019 Filomat citer still require access/body comparison. Readable related
sources include 1610.04162, 1801.08634 and the ScienceAsia2017 article; their full
scope clearance is NOT inferred from a keyword search. No external posting or
communication has occurred.

## Historical scalar-only checkpoint (superseded below)

formal/RadicalSign.lean now proves scalarDefect_lt, the literal radical expression
above is less than −17000. The proof uses coarse rational bounds a<=441/10000,
623/10000<=b<=624/10000 obtained by squaring and nonnegativity. Its rational upper
bound is exactly −1763270875137191128175507/102858162597360173056 < −17000.
Lean4.34.1 with pinned mathlib d13f23b... compiles with warningAsError=true;
the axiom report is exactly propext, Classical.choice, Quot.sound.
This is ONLY supporting arithmetic: it does not encode Phi, positive matrix
inputs, the geometric mean or the Riccati uniqueness bridge, and is not eligible
as a source-conjecture certificate. No full strict replay or review is claimed.

The 2019 Filomat publisher PDF was subsequently obtained at the correct
33-12-10-8390.pdf URL. Its actual Theorem2.6, proof, Corollary2.7, Theorem2.10 and
Corollary2.11/Remark2.12 were compared: these are weaker power bounds (at p=2,
the usual fourth-power Pólya constant), not a first-clause refutation or the
conjectured squared constant. The eight-page body was not declared globally
cleared by keyword matching. The attempted arXiv1705.09784 is a DIFFERENT paper
(Mićić–Moradi–Furuichi on Choi–Davis–Jensen), not More accurate operator means
inequalities; the latter remains unread. Both mistaken retrievals are labeled
in provenance and cannot support a novelty PASS.

## Full formal and manuscript checkpoint, 2026-10-27

The scalar-only limitation above is now discharged for the FIRST clause. Nine
modules and100 declarations prove the literal finite-dimensional universal
assertion false: SourceCounterexample.source_counterexample_329636_first
(namespace SquaredPolya) has no residual premises. The concrete positive input
bounds, full-complex-algebra unital positive map, actual CFC square-root geometric
mean, positive Riccati uniqueness, both input/output mean evaluations, genuine
quadratic form and strict negative sign are all proved. Fresh isolated strict
replay checked pinned dependencies and warningsAsError; all9 logs0 bytes; only
propext/Classical.choice/Quot.sound. Every printed type/axiom report was read by
the parent. Frozen receipt/types are verification/parent100-audit.json and
parent100-Checks.log. The manuscript main.tex/paper.pdf has2 clean pages, all
rendered/read, with all limits and credit0 stated. No formal second-clause, CP
stronger-than-positive, or optimal-constant assertion is counted. Full independent
source/math/formal/novelty/manuscript review, packet assembly and extracted replay
still remain; no acceptance or priority claim. The published LAA body and the
2018 More accurate operator means inequalities remain unread, despite public
metadata showing open archives: full-text API requires a key and web routes are
bot-blocked. The negative prior examples were independently recomputed; do not
repeat the withdrawn second-clause prior-resolution claim.
