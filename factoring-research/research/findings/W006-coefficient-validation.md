# W006 coefficient validation

Date: 2026-10-08. Independent review of branch A only. All deductions here are
review findings for parent disposition, not a promotion of the global research
claim. Verified new end-to-end factoring improvement: **NONE**.

## Symbolic audit completed before execution

**A1 is correct on its stated promise.** Write t=N-1 and m=t/2. Base digits
below are listed most significant first. For q, the digits of t and m are
(p-1,q-1) and ((p-1)/2,(q-1)/2). Both digit-binomial factors are nonzero modulo q.
For p they are (1,q-p-1,p-1) and (0,(q-1)/2,(p-1)/2). The difference between
the middle lower and upper digits is (2p+1-q)/2>0. Lucas therefore gives
C(t,m)=0 modulo p and nonzero modulo q, hence gcd(C(t,m),N)=p.

The exact valuation also checks. At level p,
floor(t/p)=q-1 and 2floor(m/p)=q-1. At level p^2, t is between p^2 and
2p^2 while m<p^2, so the difference is one. Higher levels vanish since
t<2p^2<p^3. At q the first-level difference is (p-1)-(p-1)=0 and t<q^2.
Thus v_p(C(t,m))=1 and v_q(C(t,m))=0. This includes p=3,q=5.
For completeness, Lucas's identity follows directly from
(1+X)^t = product_i (1+X^(p^i))^(t_i) over F_p: digit exponents are less
than p, so extraction gives the digit-binomial product without assuming an oracle.

**The acquisition limitation is real, and representation-specific.** Since
2^t/(t+1) <= C(t,t/2) <= 2^t, an exact integer output has Theta(N) bits.
This is an output-size obstruction for exact materialization, not a lower bound
for modular computation. Lucas evaluation needs the unknown prime bases.
Factorial division modulo N is not generally legal: its denominator contains
nonunits. An exact lift must charge its precision; detecting nonunits may itself
return a factor, but that search is paid work. No lower bound for every modular
coefficient algorithm is asserted.

**Cyclic powering computes the advertised sum.** Reduction by the monic
X^L-1 maps X^k to X^(k mod L) over Z/NZ, whether or not N is prime.
Thus the coefficient at r is precisely
S_r=sum_(0<=k<=t, k=r mod L) C(t,k) modulo N. Schoolbook convolution and binary
powering need O(L^2 log N) modular multiply-adds, using O(L log N) core working
bits for L<=N (as here); raw products have at most twice the modulus bit width.
With schoolbook integer multiplication/division this is an O(L^2(log N)^3)
bit-arithmetic bound, plus O(L(log N)^2) for classical gcds and loop/index costs.
The trace and exact evaluator add storage and time separately; they are not the
core O(L log N) working-space claim. Polylogarithmic L would give a polynomial
trial, but no success guarantee follows from this cost bound.

**L=2 never splits odd N>1.** Evaluating at 1 and -1 gives
S_0+S_1=2^t and S_0-S_1=0. Since 2 is invertible modulo odd N,
S_0=S_1=2^(N-2), a unit.

**The proposed L=4 obstruction is correct, with explicit transform signs.**
Suppose p=1 mod 4 and q=2p-1 are prime. Then p>=5, q=1 mod 8, and
t=(p-1)(2p+1)=((q-1)/2)(q+2), with 4 dividing t. Work separately in the two
fields and choose i^2=-1. In evaluation order (1,-1,i,-i), the p-vector is
(1,0,1,1): t is divisible by p-1 and all bases 2,1+i,1-i are nonzero.
The value at -1 is **zero**, since t>0.

Over F_q, 2^t=1 by the quadratic character of 2 for q=1 mod 8.
Both (1+i)^t and (1-i)^t are signs, because t is an odd multiple of (q-1)/2.
They agree: (1+i)/(1-i)=i and i^t=1. Write their common value a in {1,-1}.
Inverse transformation in coefficient order 0,1,2,3 gives
(1+2a,1,1-2a,1)/4. For p take a=1. For q either sign merely exchanges
the even-position numerators 3 and -1. Every numerator is nonzero for p,q>3,
so every coefficient is a unit modulo pq. There is no infinitude assertion for
these prime pairs; 37*73=2701 is the designated member. Field roots are used
only in this proof, never computed by the candidate.

These obstructions do not determine L=8 or L=16, so there is no symbolic reason
to skip the authorized full screen. No case, degree, limit or candidate is changed.

## Primary prior art and exact scope

Granville's [Binomial coefficients modulo prime powers](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/granville.pdf)
is primary research for the prime-power generalization and its computation.
I visually read PDF pages 1,2,8,9 (the whole 24-page file was retrieved, not wholly
read). Pages 1–2 state Lucas/Kummer background and the prime-power theorem;
pages 8–9 give Proposition 1 and the beginning of section 3 through its three-step
algorithm and operation count. In that paper's notation the modulus is p^q:
its displayed count is O(log^2 n+q^4 log n log p+q^4 p log^3 p) elementary
operations. The prime is given; the p-dependent term is not polynomial in log p.
This does not supply an evaluator for a composite modulus with unknown factors.
The PDF's theorem statement has the apparent typo m=n+r; the intended relation
is n=m+r. The review uses its own valuation calculation above. No historical
novelty for A1 is claimed; the Lucas 1878 original was not retrieved/read.

Also read Granville's author-hosted table of contents, introduction at the SFU
mirror, and retrieved author HTML pages for [generalized Lucas](https://dms.umontreal.ca/~andrew/Binomial/genlucas.html),
[computation](https://dms.umontreal.ca/~andrew/Binomial/modptoq.html), and references.
HTML formula images were missing in text extraction, so the PDF pages above,
not those incomplete equations, ground the technical statement. The PDF's text
extraction was garbled; local page renders resolved it. Rendering emitted a
Type-3-glyph bounding-box warning for pages 1/9, but their formulas were legible.

[Agrawal–Kayal–Saxena, PRIMES is in P](https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf)
already uses powers of X+a modulo (X^r-1,n). Read the web-returned excerpts around
equations (3)–(5), the quotient-ring argument (PDF pages 4–6), and section 5's
powering-cost paragraph (page 6; web lines 413–435); this was not a full-paper
audit. This prior art supports the routine nature of the quotient-ring primitive,
not coefficient-gcd factor separation. No AKS factoring guarantee is imported.

The bounded web discovery used two two-query searches for Lucas/Granville
bibliography and computation. Unopened secondary search results were leads only,
not evidence. This is not an exhaustive novelty search, nor a survey of the best
known arbitrary-composite modular-binomial algorithms.

Local read scope: full root AGENTS.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md,
docs/SPECIFICATION.md, README.md, scripts/check.sh; research/STATE.md lines 1–180
read explicitly (an earlier all-file output was truncated and is not claimed as
a full read); full research/hypotheses/W006.md and W006-coefficient-prereg.md;
full research/findings/H007-disposition.md. File-name inventories found no
applicable nested instruction file. No H007 solver/report is reopened; no
reflection branch audit, shared solver/Lean/STATE/registry edit or delegation.

## Frozen execution and results

**Disposition: the implementation passed this screen; pointwise coverage by the
fixed degree menu is rejected.** All 48 attempts completed: 16 FACTOR, 32 NO_FACTOR,
0 UNKNOWN, 0 failed and 0 unstarted. N=2701 has NO_FACTOR at all four degrees.
The exact central control returned 37 there. All 48 cyclic vectors match the
independent exact-row folds, all 48 row central coefficients equal math.comb,
and all 32 promised-input controls (eight inputs repeated across four degrees)
match A1. Every returned factor is proper and divides its input.

The table records the first proper gcd, or NF=NO_FACTOR. No unknowns are omitted.

| N | Evaluator-only factors/type | Exact central gcd | L=2 | L=4 | L=8 | L=16 |
|---:|:---|---:|:---:|:---:|:---:|:---:|
| 77 | 7*11 | 7 | NF | NF | 7 | 7 |
| 143 | 11*13 | 11 | NF | 11 | 11 | 13 |
| 221 | 13*17 | 13 | NF | NF | 13 | 17 |
| 437 | 19*23 | 19 | NF | NF | 19 | NF |
| 899 | 29*31 | 29 | NF | 29 | 29 | 29 |
| 1763 | 41*43 | 41 | NF | 41 | 41 | 41 |
| 2701 | 37*73 | 37 | NF | NF | NF | NF |
| 3599 | 59*61 | 59 | NF | 59 | 59 | NF |
| 49 | prime power 7^2 | 1 | NF | NF | NF | NF |
| 121 | prime power 11^2 | 1 | NF | NF | NF | NF |
| 97 | prime | 1 | NF | NF | NF | NF |
| 127 | prime | 1 | NF | NF | NF | NF |

Balanced-input successes by degree are 0/8, 4/8, 7/8, 5/8; failures are
8/8, 4/8, 1/8, 3/8. Coverage of this particular balanced list is 7/8.
These are exact finite counts, not estimates of an input probability or exponent.
Larger degree does not give monotone success: 437 and 3599 split at L=8 but
not at L=16. Even successful folded gcds need not preserve A1's smaller prime:
143 and 221 return their larger primes at L=16. At L=4 all eight central-class
gcds are one; its four successes occur at other positions. For the controls,
all gcds are one except N=49,L=8,index=0, whose gcd is 49, correctly not a factor.

The single supervisor invocation was
`timeout --signal=KILL 60s python3 -B research/findings/W006-coefficient-validation-screen.py`.
It exited 0 in 2.744625 seconds by its final log (2.727448 seconds at the last
saved ledger timestamp). Maximum cold attempt time was 0.059525 seconds.
Maximum candidate multiply-add count was 4,352, total 48,960; the largest attempt
used 12 exponent bits and 17 convolutions. Reduced operand width was at most
12 bits, raw multiply-add width 24 bits. Candidate elapsed sum was 0.054271 seconds;
independent central controls totaled 0.022102 seconds and row controls 0.200531 seconds.
These timings include the specified tracing/instrumentation and are not speedup
comparisons. Exact-control coefficients reached 3,592 bits, separate from candidate
width. Maximum worker traced peak was 632,877 bytes; supervisor peak was
3,160,598 bytes. Largest attempt stream was 47,444 bytes; all worker streams
totaled 481,655 bytes, and the ledger was 741,616 bytes. No resource cap fired.

Durable evidence:

- [Frozen protocol](W006-coefficient-validation-protocol.md), byte-identical to
  the supplied preregistration; [instrumentation details](W006-coefficient-validation-instrumentation.md).
- [Candidate source](W006-coefficient-validation-candidate.py),
  [evaluator/supervisor](W006-coefficient-validation-screen.py), and
  [pre-execution SHA-256 manifest](W006-coefficient-validation-freeze.json).
  All four frozen hashes were checked unchanged after execution.
- [48-attempt outcomes](W006-coefficient-validation-outcomes.json), linking all
  48 individual attempt JSONL streams; [one-shot start marker](W006-coefficient-validation-execution-started.json)
  and [execution log](W006-coefficient-validation-execution.log). All residues,
  all 360 tested gcds, step records and evaluator alias lists are retained.
- [Project check log](W006-coefficient-validation-check.log): scripts/check.sh
  exited 0 after scratch source was written and before the screen, outside its
  60-second cap. All 12 Python tests, source audit, Lean build and axiom audit passed.
  This checks repository integration; it is not a Lean proof of the new mathematics.
- [Saved-evidence verification](W006-coefficient-validation-evidence-validation.json)
  independently checks the fixed order, all 360 recorded gcds, every returned
  factor, convolution counts, alias sums, controls, terminal records and frozen
  hashes. Every check passed. [Results matrix](W006-coefficient-validation-results.html)
  is a display of the saved ledger, not a second computation.

No candidate dry run, rerun, adaptive extension or second screen occurred.
Post-run processing read the saved outcomes only; it did not recompute binomial
rows or execute candidate powering. The implementation remains reviewed trusted
code with soft allocation accounting, not an OS memory or isolation guarantee.

## Exactly how the aliases erase the selector

For the decisive failure N=2701, t=2700 and m=1350, the exact central residue is
2257 modulo N: it is zero modulo 37 and 67 modulo 73. Let A_L be the sum of all
noncentral binomial coefficients whose indices equal m modulo L. The actual
folded central-class coefficient is C(t,m)+A_L, not C(t,m).

| L | Central class r | Noncentral aliases | A_L mod N | A_L mod 37 | S_r mod N | S_r mod 73 |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 0 | 1350 | 1795 | 19 | 1351 | 37 |
| 4 | 2 | 674 | 1193 | 9 | 749 | 19 |
| 8 | 6 | 336 | 855 | 4 | 411 | 46 |
| 16 | 6 | 168 | 96 | 22 | 2353 | 17 |

The complete alias sets, including each residue, are in each outcome's
`control.central_aliases_index_residue_mod_N`. Exactly, their indices are
{0+2j:0<=j<=1350}, {2+4j:0<=j<=674}, {6+8j:0<=j<=336}, and
{6+16j:0<=j<=168}, respectively, always omitting 1350.
This identifies the erased information without an expanded experiment.

The Lucas pattern makes the error of representation especially visible here:
2700 has base-37 digits (1,35,36). For 0<=k<=2700 the coefficient vanishes
modulo 37 exactly for **1332<=k<=1368**. Outside that block, with digits
k=a*37^2+b*37+c, its residue is
(-1)^(b+c)(b+1) modulo 37 (a=0 or 1, b<=35, c<=36).
This uses C(35,b)=(-1)^b(b+1) and C(36,c)=(-1)^c modulo 37.
Thus L=16 keeps only three indices from the zero block in the central class:
1334,1350,1366. Its other **166 aliases are nonzero modulo 37**, and their sum
is 22 modulo 37. The zero is destroyed by adding those aliases, not by a faulty
modular exponentiation. The other three degrees have respectively 18,8,4
noncentral aliases in the zero block; their outside-block sums are the nonzero
values 19,9,4 displayed above. All positions, not only the central class,
have unit gcds for this N at every menu degree.

The N=2701 folded vectors in coefficient order are:

- L=2: (1351,1351).
- L=4: (602,2026,749,2026).
- L=8: (301,2105,338,2105,301,2622,411,2622).
- L=16: (539,2569,169,2237,2463,2494,2353,2494,
  2463,2237,169,2569,539,128,759,128).

The failed assumption is that congruence classes modulo a small known L preserve
a carry condition in an unknown prime base. They do not in this screen. Moreover
all four quotient vectors are determined by F_16, because 2,4,8 divide 16; extra
coarse views add no independent coefficient information. On arbitrary input
polynomials, X^(m+16)-X^m is already a kernel witness that changes the central
coefficient while leaving all four folded vectors unchanged. This is a statement
about lost information in this representation, **not** a lower bound for the
special structured polynomial (1+X)^t, nor for arbitrary operations on F_16.

## What could change the conclusion

A replacement must compute a quantity with proved factor separation and pay
for isolating it. One actual correctness reference is binary powering modulo
(N,X^(m+1)), retaining degrees 0 through m with truncated ordinary convolution.
The degree-m coefficient is then exactly C(t,m) modulo N, without nonunit
division or cyclic aliases. Its vector dimension is m+1=Theta(N), schoolbook
cost O(N^2 log N) modular multiply-adds and O(N log N) core storage bits. It was
not executed and gives no useful factoring bound. An improved construction would
need to replace that paid state with an explicit smaller representation or an
equivalent separating computation, prove what information survives, and charge
all precision/transition work. A name such as trace, Hasse coefficient or
holonomic recurrence supplies none of those steps.

The precise next proof obligation is an efficient, factor-oblivious central-block
isolation or equivalent modular evaluator with a complete bit-cost analysis.
The fixed menu is closed by its retained counterexample; automatic larger-degree
search is neither justified by this result nor authorized by this task. A1 and
the L=2/L=4 symbolic obstructions survive the audit; all general compressed
coefficient routes remain outside this finite rejection. No new best factoring
bound or useful all-input success law is verified.
