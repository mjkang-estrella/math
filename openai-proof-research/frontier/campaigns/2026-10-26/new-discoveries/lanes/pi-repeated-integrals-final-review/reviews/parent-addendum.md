# Parent integration of preliminary review

The complete review and provenance were read. Source/math/bounded-novelty and
eligibility PASS are adopted with the original access and priority limits.
This is one prospective resolution of the all-order source conjecture using
standard moment-cone techniques; no claim of new general moment machinery.
Credit remains0 until the full literal Lean endpoint, manuscript, final review
and extracted packet replay. Current accepted campaign tally is17, superseding
the review's historical16.

The original10-file freeze and original review are preserved. The formal
development is a later phase, not covered by that preliminary review.

## Minor mathematical qualifications to the review

1. R1's suggested justification of int C_(0,1)=int C cannot be adopted as
written: an arbitrary interior vector has not yet been proved to have an
atomless representative at that point in the alternative argument. Use the
ordinary convex interior/closure identity instead: the open-interval cone is
convex, spans the moment space by Vandermonde, and has closure C. Its interior
therefore equals int C. The primary A-open/A-dense proof needs no such detour.

2. The complete degree-two moment-cone interior conditions are

    m>0,  m1^2<m*m2,  m2<m1.

The review's list omitted the last inequality, which is required for support
in[0,1]. It also follows that0<m1<m. Under
m=c, m1=c-b, m2=c-2b+2a, these conditions become exactly the source's
0<2a<b and b^2<2ac. Thus the conclusion of its W_2 cross-check is right, but
the intermediate list as printed is incomplete. No numerical scratch evidence
is needed for this exact algebraic comparison. W_1 similarly gives0<a<b.

3. Atomlessness is sufficient, not necessary, for interiority. A single
interior atom is an interior point when n=0 or1; for n>=2 its zero quadratic
places it on the boundary. Two distinct interior atoms are interior for n=3.
No converse to atomless implies interior will be used. The review's broad
informal 'an atom would kill interiority' phrase is not adopted.

4. R2 is addressed by the classical accessibility argument: if x lies in
int(cl A), choose a in A and a point y=a+t(x-a) in cl A with t>1 close to1.
Then x=(1-1/t)a+(1/t)y belongs to A by openness, convexity, and accessibility
from an interior point to a closure point. Mathlib's
Convex.interior_closure_eq_interior_of_nonempty_interior is the intended
formal fact. R3's numbering correction is adopted: diDio Cor2.7 in arXiv
equals Cor3.1 in the published paper.

5. The parent's fresh full MathDB API record and all empty arrays are the
authoritative live-record evidence. No claim depends on a reviewer webpage URL
or on the unrelated mathdb.org domain. Empty records/searches never certify
novelty. The source's conditional sequel remains an explicit predecessor,
regardless of whether a citation index includes it.

These qualifications concern supplementary exposition, not the load-bearing
moment-cone proof. A new final review must check the completed formalization.
