# Routes with zero proposed credit

## 354420: a short incidence-counting bridge

Source: Abiad–Carmona–Encinas–Jiménez, arXiv:2204.13186v1, Case 5,
Proposition 18 and Conjecture 21. The actual source PDF is preserved, with
the HTTP receipt and SHA-256 in receipts/. This is an ordinary argument,
not a Lean endpoint, and is explicitly not proposed as a substantive discovery.

Suppose a nontrivial 2-(v,k,lambda) design has exactly the two block
intersection sizes 0 and y, with 0<y<k, and lambda>0. Take disjoint blocks
B and C. Choose a point in each. Some block D contains the two chosen
points, so it meets both B and C in y points. Since B and C are disjoint,
2y<=k.

Fix a block B and a point a outside it. Count pairs (b,D) where b is in B
and D contains a,b. There are k*lambda pairs. Every block through a that
meets B contributes y pairs. Thus k*lambda<=r*y, where r is the replication
number, and consequently lambda<=r/2.

The source's Proposition 18 says that its incidence graph has the M-property
if and only if

    (k-1)(r-lambda)((k+r)^2-lambda*k) <= k^2*lambda^2.

But (k+r)^2>=4kr and lambda<=r/2 give

    (k-1)(r-lambda)((k+r)^2-lambda*k)
      >= (7/4)(k-1)*k*r^2
      >  (1/4)k^2*r^2
      >= k^2*lambda^2,

where strictness uses k>=2, r>0 and 7(k-1)>k. Hence that criterion cannot
hold. This argument relies on the source's characterization; it is not an
independent proof of Proposition 18 or its group-inverse formula.

This is precisely the campaign's short source-ingredient/classical counting
bridge profile. No independent significance review has occurred; the lane
recommends zero credit and no Lean investment. The parameter scan in
logs/design-1.log checks 164181 necessary tuples with 2<=k<=150,
k<r<=1000, 1<=y<=floor(k/2), the source parameter identity and divisibility.
None passes the inequality. This is not enumeration of all designs.

## 355215: printed-example amplification is ineligible

Source: Barrett–Cameron–Evans–Hall–Kempton, arXiv:2206.15410v1,
Figure 3 and Conjecture 6.7. The source itself reports a five-vertex graph
with spread 5.035>5. A uniform independent-set blow-up is an immediate
route to amplifying that printed example: replace each vertex by t twins
and each arc by all t^2 arcs. Its Laplacian is

    L_t = t D tensor I_t - A tensor J_t.

On vectors constant on each twin class, the compression is tL. The same
embedding preserves the subspace perpendicular to the all-ones vector.
Thus the restricted numerical range contains t times the original one,
and the spread is at least t times the old spread. Any rigorously certified
base example with spread>5 therefore excludes a universal n+C bound.

No exact certification of Figure 3's numerical value was attempted here;
the point is that this route is a short augmentation of the source's own
printed obstruction and is disallowed independently of numerical accuracy.
No new counterexample, full proof, or Lean endpoint is claimed.

## 355005: keep the zircon premise

The literal MathDB span omits the essential source condition that [u,w]
is a zircon. Umutabazi arXiv:2206.06538v1 Conjecture 4.2 explicitly includes
it. Conjecture 4.5, verified in type A_n for n<=8, is a different smoothness
criterion which implies the zircon conjecture in type A. Example 4.11
and the printed B2 failure concern neighboring claims and cannot count
as a new refutation of the reserved source question. No search against the
defective unrestricted paraphrase was undertaken.
