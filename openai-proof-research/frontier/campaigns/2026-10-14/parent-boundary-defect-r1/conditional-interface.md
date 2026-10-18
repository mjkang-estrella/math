# Fixed-boundary cone pictures: parent author-side interface

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Assistance to
structural r49, not an independent review, scope freeze, novelty verdict or
campaign acceptance. Root read source196 topology.tex and planar.tex in full.
Source197 and the primary small-cancellation bodies were not read by root in
this step. The agent independently proposed the same boundary-defect route;
the overlap is disclosed rather than counted as independent validation.

## Area conversion does not require area-minimal pictures

Fix each finite labeled graph component Lambda and a spanning tree in it.
Use as ordinary relators the labels of the fundamental loops of the
non-tree edges, based at one chosen graph vertex. These give the same
quotient group as coning Lambda, by the source's relative cone-substitute
construction. A closed lifted path p of length m expresses, after the
appropriate basepoint conjugation, as a word of at most m letters in that
free basis: only traversals of non-tree edges contribute letters.
Its image label therefore has ordinary relator area at most m.

For any cone picture with outer word v and total inner lifted length H,
fill each inner boundary this way. The complementary punctured disk maps
to the rose, so these fillings give an ordinary van Kampen filling of v
with area at most H. No bound on the original null-homotopy's area and no
area-minimality assumption enters this conversion.

For a fixed null word v, minimize H over cone pictures of that exact word.
The nonempty set of integer lengths has a minimum. Tighten inner loops
and remove constant ones. The source's same-lift inner-to-inner band
surgeries preserve the outer word and strictly lower H. In a self-band
case keep the component containing the outer boundary and cap through
the same contractible cone. The other component need not be essential
and may be discarded. Thus every retained inner-to-inner paired edge
has distinct underlying graph lifts. Inner-to-outer bands are not
cancelled, since such surgery changes the prescribed outer word.

## Boundary deficit and comparison intervals

Freely and cyclically reduce the outer word first: relator area does not
change on taking a conjugate, and its new length does not increase.
If the cyclic reduction is empty its area is zero. Otherwise a null
word has a cone picture with at least one inner loop, because a nonempty
freely reduced word cannot fill in the rose. Thus H>=L by girth.

Add one formal outer disk carrying that cyclically reduced signed-letter
word. No lift of that disk's boundary into Gamma is asserted or needed
for the planar count. The full transverse arc pairing remains planar.
The source's good-gap/Euler calculation uses signed inverse pairing and
the absence of adjacent inverse letters; the latter holds on the outer
disk in the rose. It does not use an actual graph lift for this count.

Split only long inner paths as in the source, into N' pieces, and keep the
outer boundary as one piece. The comparison-interval bound is at most
6(N'+1). Remove the outer disk and every pair incident to it. At most
|v| inner occurrences become unpaired. Outer-to-outer arcs add no inner
deficit. Every removed pair is a whole comparison interval, since the
interval cuts respect the inner pieces and the one outer piece. All
remaining comparisons still concern actual inner graph lifts.

Every inner piece has at least L original occurrences, so N'L<=H.
Together with H>=L this gives

    number of retained comparison intervals <= 12 H/L.

The remaining piece graph is planar, and the source's separator applies.
Using its unchanged U, D, eta, K and C_2=192, with the source's deliberately
loose bounds, retained clusters satisfy

    sum H_Z >= 15H/16,
    sum b_Z <= epsilon H/16 + |v|,
    sum I_Z <= 12H/L,
    H_Z <= K(U+D)L.

The first deficit includes the deleted-piece partners and unpaired
closures; |v| is the additional exterior deficit. If
H>=32|v|/epsilon, clusters with b_Z>epsilon H_Z have total length at
most 3H/32. Those with I_Z>C_2 H_Z/L have total length at most H/16.
At least 25H/32 remains. Every remaining cluster contains a cyclically
immersed loop and hence has length at least L. There is no short
exceptional graph-path cluster to subtract. Thus one obtains precisely
a bounded all-cyclic pattern of the type excluded by the source's
bounded-pattern event, with the same fixed parameter order.

Conditional on the full stated source pattern interface and the
fixed-boundary picture adaptation above, this yields H<32|v|/epsilon,
and the independent area conversion yields a linear Dehn bound.

This note isolates the proposed extension of the source proof. It does
not assert that the original no-spherical-arrangement statement alone
implies a Dehn bound, or that arbitrary aspherical finite complexes have
linear fillings. The usable quantitative input is the stronger
near-paired bounded-pattern exclusion and the closure/separator bounds.
Actual source197 compatibility, full theorem scope, primary attribution,
and independent proof/contribution gates remain separate obligations.
