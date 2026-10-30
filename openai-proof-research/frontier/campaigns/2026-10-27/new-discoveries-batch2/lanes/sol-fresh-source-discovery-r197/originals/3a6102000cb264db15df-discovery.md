# Fresh arithmetic source; no full resolution

Zero nominees. The conjecture below is unresolved in this lane. No partial case,
helper, adaptation, formulation correction, finite test or route obstruction is
offered as a discovery. Root's investment and acceptance gates are untouched.

## Literal source and current public coverage

Lien-Hung Su, *The Read-Once Factorial-Divisibility Conjecture: Algebraic Proofs
Through Six Inputs*, Zenodo version 2.0, https://zenodo.org/records/21853500,
DOI https://doi.org/10.5281/zenodo.21853500. Definition 2.1 and Conjecture 2.2,
PDF p2: for **every** integer n>=1 and **every** set S of n distinct integers,
there exists a fully parenthesized expression with binary operations +,-,*
whose leaves are in bijection with S and whose integer value is in n!Z.
Zero is permitted. Unary negation, division, powers, constants and repeated
leaves are not supplied as extra operations. The expression may depend on S.
Neither universal validity at a fixed n nor improved small-case moduli resolve
this full target.

Actual retrieval was October 30, 2026 UTC (October 29 Los Angeles), as recorded
in http.jsonl. The record displays publication August 9, 2026; API creation
and update are August 8. These different date fields are preserved. The current
latest-version endpoint redirects to API record21853500 and marks version2.0
as last. This is a bounded current-source observation, not an assertion that no
unlinked later paper exists. No journal version was established.

Before sustained mathematics, followed actual source-facing links: the v2 PDF
and full companion source ZIP. Read actual PDF pp1-10, including Definition2.1,
Conjecture2.2, Lemmas3.1-3.5, Theorems4.1-4.6,5.1-5.2,6.1, section7's
frontiers, sections8-10, and AppendixA's three-input and selected four-input
proofs. Scope p2 was also visually inspected. Read README_FIRST and the complete
VERSION_2_CHANGELOG, retained extracted LaTeX for the other appendices, and
read the bibliography. Not every later appendix proof was independently
audited. The source's main theorem covers exactly 1<=n<=6. Its conclusion
explicitly leaves the full conjecture open, first finite case n=7. The
changelog preserves this scope while correcting small proofs and strengthening
four-input guarantees. None of that public mathematics is nominated here.

Bounded public searches for the exact title, author and read-once/factorial
aliases located this record and no separate full-scope proof lead. Search
silence is not verified absence. The source's actual public proof package was
read before trying to extend it; no unread abstract was treated as a resolution.

## Project freshness and fixed registries

Before downloads, queried exact title, DOI/record ID, author and claim aliases
against entire retained original SUMMARY/discovery/PROOF/review/DECISION bodies.
The qualified r150/r147 baseline was reused, then the qualified r153 changed
roles were merged and new/changed original roles refreshed. Final exact
Su/read-once queries have no retained-body hit. Original r111-r113 scientific
bodies remain in scope, explicitly listed in the query receipts. No size cutoff
or snippet-only absence test was used. frozen/private/core/context/extraction
copies are excluded as generated roles. An initial inherited traversal had
included frozen copies; the corrected final traversal removes them. This is
project freshness within the retained role scope, not workspace-wide semantic
or worldwide literature clearance. history-delta.json describes changes
against the inherited indexes, not a reissued unchanged inventory.

An initial subsum-polynomial search hit original denominator-dyadic-r1,
discrete-r6 and r124 reports. Their original dispositions were reopened; the
family was retired without new downloads or sustained mathematical work.
Broad factorial-divisibility aliases also produce unrelated Jacobi/MMPP
text hits; the narrower exact Su query is the freshness evidence. No result
from these old families is repackaged. r154 and Kazemi work remain separate.

Registry-screen.json retains fixed Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c
and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a indexes. No HEAD chase.
The aa026->a19a and a19a->490f compare lists are both capped300; narrow
walks do not clear omitted paths. Lexical scans do not clear unnamed semantic
subsumers. Two actual plausible factorial theorem bodies were downloaded at
fixed Omega and read in full: FactorialSquareDivisibilityPrimePower concerns
the exponent of n! dividing (n²)!; PerryLeastFactorialDivisibleByPrefixLcm
concerns lcm(1,...,n) dividing p!. Their literal statements do not construct
read-once expressions on arbitrary inputs. Other lexical leads were not all
body-read. No complete registry or classical exclusion is asserted.

## Sustained route 1: factorial induction by signed pairs

The source Lemma3.3 says that among n integers, either one is divisible by n,
or two have sum/difference divisible by 2n. This follows because, modulo2n,
the other residues occupy only n-1 nonzero signed classes.

Suppose the conjecture is available on smaller sets. In the first branch,
multiply the n-divisible leaf by an expression divisible by (n-1)! on the
remaining inputs. This is a legal n!-multiple. In the pair branch, however,
the same induction gives only

    (2n)*(n-2)! = (2/(n-1))*n!.

This does not imply n!-divisibility once n>=4. The pair expression is a
single chosen integer whose extra divisibility cannot be assumed. At n=7,
the source five-input guarantee gives 14*120=1680, short of5040 by a factor3.
The surviving task is to choose the 14-divisible pair simultaneously with a
360-divisible complement, or otherwise exploit additional factors in the
chosen pair. The source's separate five-odd 180 and240 guarantees do not
license a common 360 guarantee: they can use different expression trees.
The all-n problem needs substantially more than repeating this induction.

Attempted strengthening: partition into singleton leaves and pair sums or
differences, then multiply all blocks, choosing pairings to allocate the
prime-power factors of n! simultaneously. For seven inputs the demanded
valuations are v2>=4,v3>=2,v5>=1,v7>=1. Pair choices that produce a factor7
can consume leaves needed to produce5 and the two factors3. Local signed
collisions separately modulo each prime do not establish one common matching.
A finite dynamic program tracks gcd(product,5040) over every such partition.
100 deterministic sampled unit tuples admit a matching; no invariant proving
this for all tuples, still less all n, was found. No larger sweep is substituted
for that absent argument. This route remains open rather than falsified.

## Sustained route 2: fixed divisors and Vandermonde transport

Read actual Bhargava2000, *The Factorial Function and Generalizations*,
Theorems2-3 on printed p784, retained PDF and text. Theorem3 says that for
n+1 arbitrary integers the product of all pairwise differences is divisible
by 0!1!...n!. It is genuine classical factorial divisibility, but its polynomial
reuses every input n times. It is not a legal read-once expression. There is
no proved process extracting a suitable disjoint collection of factors while
preserving the needed simultaneous valuations. Even such a process would
need the exact factorial and leaf counts, not just an inequality of total
valuation. No complete classical bridge and therefore no classical exclusion
of Su's full conjecture is claimed.

A universal *fixed* expression template cannot repair this route. Every
read-once expression on distinct formal variables expands into a nonzero
multilinear polynomial whose nonzero coefficients are +/-1. Inductively,
addition/subtraction combines polynomials on disjoint nonempty variable sets,
so monomial supports cannot cancel; multiplication has unique support unions.
If every evaluation of this polynomial were divisible by m>1, Boolean-grid
finite differences would make each coefficient divisible by m, contradiction.
Restricting the actual inputs to be distinct does not save a fixed template:
any prescribed tuple of residues modulo m has pairwise distinct integer lifts,
and polynomial values modulo m are unchanged by those lifts. Thus adaptation
to the input residues is essential. This elementary method obstruction is
uncredited and does not refute the existential source conjecture.

Finally, separate prime-power or modulus solutions cannot simply be patched
by CRT on expression choices. Already on leaves1,2 the obtainable values are
3,-1,1,2. Multiples of2 and3 are separately attainable but no multiple of6 is.
CRT combines numerical residues when parameters can be varied; it does not
combine two competing trees with a common read-once leaf budget. This example
does not refute the source target2!=2.

## Diagnostics, objection, falsifier and precise gap

Run sh run-checks.sh. Exact modular subset dynamic programming combines
x+y,x-y,y-x,xy over bipartitions, storing an expression witness for each
reachable residue. Every tree has a root bipartition, so the recurrence is
complete when exhausted. The full root searches only residue0. A two-million
pair-operation cap per case reports incompleteness rather than absence.
All four chosen seven-input unit tuples return witnesses well below that cap;
each is independently evaluated over integers and checked to use each indexed
leaf exactly once. For example the first tuple has

    ((167+283)*239)*((307-389)+331+311) = 60228000 = 11950*5040.

The restricted singleton/pair product checker tracks attained gcds by exact
recursion and tests100 deterministic tuples. These are finite consistency
checks only; no universal parameter range or counterexample is established.

Strongest objection: all completed deductions are classical facts, elementary
route obstructions, or finite witnesses. None supplies a new full-scope result.
Strongest falsifier of the source: one n and n distinct integers with0 absent
from the **complete** read-once reachable set modulo n!, with no truncated
subtree or operation budget. A failed restricted matching would only falsify
that restricted strategy, not Su. A positive resolution needs a single
adaptive all-n construction with a proved leaf budget and simultaneous
prime-power divisibility. That is the precise mathematical gap.

All retained HTTP requests succeeded200; no403/429/challenge was encountered
or bypassed. Initial tool-output truncations are not used as source or absence
certificates. The unchanged prescribed guard enforces AS and sampled group
RSS512MiB, CPU210s, wall230s, nominal40ms, BLAS/OpenMP1. Sampling does not rule
out unsampled transients. No Lean or manuscript was started. Final science
hashes exclude mutable as-read NEXT/context; the final manifest includes the
context bytes separately. Offline manifest/source verification is supplied.
