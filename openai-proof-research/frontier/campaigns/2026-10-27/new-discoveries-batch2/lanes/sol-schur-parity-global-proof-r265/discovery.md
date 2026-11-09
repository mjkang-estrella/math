# Schur parity global route: unresolved, no discovery credit

Target is Koutschan–Wong, arXiv:1904.01925v2, Conjecture 1, printed p22:
for every integer n>=12 the minimum over all two-colorings c of [1,n] of
the number M(c) of ordered triples (x,y,x+floor(y/2)) in [1,n]^3 is
floor((n^2+5)/6). Coordinates may repeat. No x<=y convention is imposed.
This lane proves the source attainment identity and some obstruction lemmas,
but does not prove the universal lower bound or give an admissible counterexample.
These helpers receive no credit. There is deliberately no PROOF.md.

## Primary scope and bounded subsumption screen

Source manuscript Theorem 5, printed pp21–22, proves a different minimum:
the three-block family R^s B^(t-s) R^(n-t), with modulus 38 corrections.
The following discussion explicitly withdraws that family restriction for
Conjecture 1 and supplies the public n=11 exceptional word RBRBBRRBRBB.
We read those actual statement and proof bodies, not just its abstract.
Its CAD/block-enumeration proof does not cover arbitrary colorings. The
attainment calculation below is a source-method adaptation, not novelty.
The source was submitted 2019-04-03; v2 was updated 2020-10-12. Its reported
Springer chapter DOI is 10.1007/978-3-030-44559-1_13.

The actual predecessor body Thanatipanonda–Wong, arXiv:1609.07639v2,
Proposition 14/Lemma 15, and Theorem 22/Propositions 25–28, uses
nonmonochromatic coordinate-pair counts and reflected pairs. Theorem 22 is
for fixed integer a>=2 in x+ay=z and has an O(n) error. The source floor
relation has a=1/2, two parity fibers and exact residue corrections.
Neither integer scope nor suppressed boundary terms may be transferred.
Metadata gives first submission 2016-09-24 and v2 update 2018-02-14;
the PDF's running journal footer is not substituted for publication chronology.

A fresh lawful arXiv query on 2026-10-30 at 16:24:40 UTC led to an actual
additional primary body: De Loera–Ventura–Wang–Wesley,
arXiv:2410.21651v1 (submitted 2024-10-29). Read Theorem 2's modular coloring
proof, Lemma 11's coordinate-pair/max-cut proof, Lemma 12 and the proof
of Theorem 5's interval/residue SDP bound. Theorem 5 is expressly for
ax-ay=z with 3<=a<=7. Even source y obeys 2z-2x=y, but the missing a=2
case and odd y (2z-2x=y-1) preclude using that theorem. Its Theorem 2 is
an upper bound for a homogeneous equation, not the target lower bound.
The max-cut reformulation is already part of that published method, so
we claim no novelty for it or for algebraic changes of its notation.

This is a bounded primary screen, not clearance of worldwide priority.
The current arXiv query returns 30 entries and 38 total hits; no inference
of absence is made from this truncated topic query. The author's primary
publication page failed TLS and was not retried. Current public proof-registry
heads remain UNKNOWN because inherited denied routes remain parked.
No GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge,
proxy, TLS-disable, browser or inaccessible-history retry was used.

## Rederivation retaining all roles

Write Y_v={2v,2v+1} intersect [1,n]. Since floor(y/2)=v exactly on Y_v,
partitioning the original (x,y) domain gives

    M(c) = sum_v sum_(x=1..n-v) [c_x=c_(x+v)] sum_(y in Y_v)[c_x=c_y].

Here v=0 contains only y=1; it contributes the number of entries having
color c_1. If n is even the last fiber contains only y=n. No y=0 or
unavailable endpoint is inserted. A mixed interior fiber has inner sum 1;
this does not permit recoloring that fiber while holding the other roles fixed.

For s_i=1-2c_i, the identity for a single triple is
4[all equal]=1+s_x s_y+s_x s_z+s_y s_z, including repeated coordinates.
Let S_j=sum_(i<=j)s_i, S_0=0, and C_v=sum_(x<=n-v)s_x s_(x+v).
Define a_v=|Y_v| and T=n^2-floor(n^2/4). Summing the three roles gives

    4M = T + sum_(y=1..n) s_y (S_(n-floor(y/2))+S_n-S_floor(y/2))
             + sum_v a_v C_v.                                      (1)

The first two terms in parentheses come respectively from x and z
paired with y, while C_v is the x,z role. Thus (1) has no frozen-role
assumption. Exhaustive complement representatives for 1<=n<=13 verify
both identities directly against original ordered triples (8191 representatives
in total, equivalent to all 16382 colorings). These are identity checks,
not a proof of the infinite conjecture.

## All-role interval exchange and a decisive obstruction

For i<j, counting each coordinate-pair occurrence gives

    w_ij = [i+floor(j/2)<=n]+[j+floor(i/2)<=n]
         + [2(j-i)<=n]+[2(j-i)+1<=n]+1+[i-floor(j/2)>=1].

Loops do not change under recoloring. If F is any set of recolored vertices,

    Delta_s(F) = M(s flipped on F)-M(s)
               = -1/2 sum_(i in F,j outside F) w_ij s_i s_j.          (2)

For an interval I=[a,b], put h_i=sum_(j!=i)w_ij s_i s_j. Then

    Delta_s(I) = -1/2 (sum_(i in I)h_i
                         -2 sum_(a<=i<j<=b)w_ij s_i s_j).

This supplies an exact, parity-aware boundary defect accounting for all
three roles. It is not a global certificate. In particular, when F,G
are disjoint,

    Delta_s(F union G)=Delta_s(F)+Delta_s(G)
                         +sum_(i in F,j in G)w_ij s_i s_j.           (3)

The last term cannot be discarded. Negative cross interactions can make
a simultaneous exchange improve even if its constituent moves worsen M.

Rigorous witnesses in the target range:

* At n=12, word 000000111101 has M=35. Its mixed fiber {10,11}
  has monochromatic replacement deltas +5 (both 0), +1 (both 1).
  Thus even choosing the better merge can increase the true count.
* At n=12, word 000110110011 has M=27. Its twelve single-flip
  deltas are (1,1,2,5,5,3,2,1,5,4,2,1), all strictly positive.
* Stronger: word 011001001101 at n=12 has M=26. Every proper nonempty
  interval flip strictly increases M. Flipping the whole interval merely
  complements the coloring. Hence allowing neutral interval moves and
  any auxiliary lexicographic defect cannot escape this state.
  The simultaneous flip [3,5] union [9,11] reduces M by 2, reaching 24.
  All 78 interval deltas and this two-interval escape are independently
  recounted from original triples in scientific-verification.json.
* Exhaustive plateau-component analysis at n=12 gives suboptimal sink
  components of sizes 5,8,1,1, at levels 26,25,26,26; at n=13 the sizes
  are 1,1,2, all at level 30 (optimum 29). Complement normalization is
  explicit, and all interval masks are generated. This strengthens the
  strict-descent obstruction but proves no large-n statement.

Neither the previously falsified PSD certificate nor generic triangle
packing was rerun. Their original witnesses remain in the frozen r262
report. No larger heuristic sweep was used.

## Exact block convolution and universal attainment

Here is an ordinary finite-sum derivation, rather than interpolation.
Set R(t)=max(t,0), Q(t)=R(t)(R(t)+1)/2. For integer m>=0, q=floor(m/2),

    H(m,t)=2(Q(q+t)-Q(t-1))-R(t)-[m even]R(q+t).

Indeed, H(m,t)=sum_(y=1..m)R(floor(y/2)+t): each fiber has weight two,
except v=0 and, for even m, v=q, whose weights are one. The telescoping
sum sum_(v=0..q)R(v+t)=Q(q+t)-Q(t-1) proves the formula, including m=0.

For x in [a,b], y in [c,d], z in [e,f], the number of triples is
the sum over y of

    R(v+b-e+1)-R(v+a-e)-R(v+b-f)+R(v+a-f-1),  v=floor(y/2).

This follows by subtracting the counts x+v>=f+1 from x+v>=e.
Replacing each ramp sum by H(d,t)-H(c-1,t) yields an exact four-term
formula. Sum it over all ordered triples of same-colored blocks; no
coordinate ordering is imposed and all repeats remain.

For the source endpoints s=floor((n+3)/6), t=floor((n+1)/2),
u=floor((5n+3)/6), substitution for n=12k+r, 0<=r<12, k>=1,
removes every floor. Every ramp argument is affine in k; its sign is
certified by its slope and value at k=1 (not sampled or fitted).
The twelve resulting polynomials are in block-identity.json. Equivalently,
for n=6q+r, r=0,...,5, they give

    M(source)=6q^2+2rq+b_r,
    (b_0,...,b_5)=(0,1,1,2,3,5)=floor((r^2+5)/6).

Consequently the published construction really attains the conjectured
value for every n>=12. This only proves the universal UPPER bound on
the minimum, and is an uncredited verification of a source construction.

The same convolution closes a structural counterexample route: stretch
each letter of the public exceptional word 01011001011 by h. Its exact
count is (85h^2-5[h odd])/4, proved symbolically for both parities (h=1
is also directly checked). For h>=2 this exceeds floor((121h^2+5)/6):
subtracting even the unfloored target gives
(13h^2-15[h odd]-10)/12>0. Thus this entire infinite structural family
cannot refute Conjecture 1. No finite-size extrapolation is needed.

## Precise remaining universal bridge

Let s be the source sign vector. For any ordered disjoint, nonadjacent
intervals I_1,...,I_l contained in [1,n], the missing inequality is

    sum_r Delta_s(I_r)
      +sum_(r<t) sum_(i in I_r,j in I_t)w_ij s_i s_j >= 0.             (4)

Every subset is a unique union of such intervals. Equations (2)–(3) show
that (4) is equivalent to the universal lower bound, with the residue
constants supplied by the attainment calculation. It remains UNPROVED;
writing it down is a reformulation, not a resolution. A successful
boundary/defect proof must control its negative cross-interaction sum
uniformly, without restricting the number of intervals or assuming an
optimal four-block coloring. The rigorous interval traps rule out the
simple monotone compression approach even with zero-cost steps. We have
not established a two-interval descent theorem, a finite-state recurrence
covering arbitrary colorings, or any asymptotic substitute for (4).

Status: HOLD, full source endpoint unresolved. No claimed discovery,
no Lean, no manuscript, no MathDB/public edits, no count change.
