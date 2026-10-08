# H024 many-giant coverage: reviewed counting, no attained gain

2026-10-08. Factory Opus proposal; native Astra independent mathematical review
completed. Root checked formulas and directly read BL section6. Separate Factory
Fable primary-prior-art/full-cost review is RUNNING (task in H024-manygiant-review).
Verified improvement NONE. No numerical coverage experiment yet admitted.

For fixed public arithmetic progressions P_ij=b_i Q+(c_i+j*s_i)G,
a signed collision solves

    (b_i−epsilon*b_l)*k = epsilon*(c_l+r*s_l)−(c_i+j*s_i).

Require nonzero denominator modulo prime q and verify. Distinct b values alone
do not guarantee both channels: b_i=−b_l disables one. Same-family NEGATIVE
collisions can be useful when b_i!=0; their candidates depend only on j+r.
With contiguous prefix lengths L_i and t=sum L_i, cross-family pairs supply
at most t²−sum L_i² scalars. Same-family negative pairs plus infinity supply
at most sum_{b_i!=0}max(0,2L_i−1). Hence

    |C_t| <= (1−1/f)*t²+2t.

This is a counting ceiling for fixed target-independent schedules, not an
attained coverage or a coordinate-adaptive lower bound. For uniform all-q
scalars and first discovery T, P(T>t)=1−|C_t|/q; summing survival probabilities
gives exact finite expected outputs, including the tail/fallback. Excluding
zero requires q−1 and its actual coverage. Integrating the ceiling gives

    E[T] >= 2/(3sqrt(1−1/f))*sqrt(q) − O(1).

The .943, .816, .770 values for f=2,3,4 are optimistic FLOORS. No shifts
attaining them were supplied. A single cap's success rate is not a mean.

H019 paired x-only generation can apply separately to each fixed stride,
but pay s_iG, b_iQ+c_iG, affine centers, offsets, support, exceptional cases,
actual block order/overshoot, stored records and checks. Fixed f with slowly
growing blocks can make setup lower-order under stated memory assumptions;
finite accounting is still needed. At equal per-key work, .90 versus .943 is
only about4.5% arithmetic improvement;10% needs c<.84853 before extra overhead.

Primary prior art: [Bernstein–Lange, section6](https://mathweb.ucsd.edu/~kedlaya/ants10/bernstein/paper.pdf)
already gives a baby and two giant progressions and reports experiments with
four giants and optimized shifts. It does not supply a uniform optimal shift
construction. Root read the actual primary PDF, not a search snippet. This
is a known direction; absence of a later paper in a bounded search is not novelty.

Next decisive gate: freeze b_i,c_i(q),s_i(q), interleaving, block sizes, cap
and fallback. Integer-only enumeration of both candidate equations and direct
infinity gives exact first discovery for every scalar. Assign each discovery
the actual completed-block cost. A partial survival sum can reject an asserted
budget; passing finite primes is not an asymptotic proof. Strongest applicable
known schedules and memory must be matched before accepting an improvement.
No EC benchmark or broad formal infrastructure is justified yet.

## Completed primary-literature review / comparator correction

Factory Fable review COMPLETED, raw report preserved separately. Root opened
the primary GWZ article and directly checked section3.1, Tables3/5 and AppendixB.
[GWZ2017](https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf)
already studies b=(0,1,2), strides(1,M,−(M+1)), with negation. Table5 reports
average constants .8926,.9053,.8961,.9048,.9207 for its tested sizes; Table3 marks
about.9 conjectural. Include this empirical comparator in future finite designs,
separately from the proved two-family2sqrt(2)/3. This is prior art, not project
progress in solving ECDLP. No proved asymptotic.9 or universal tail bound follows.

AppendixB tests a non-negated four-giant rule with strides M,−(M+1),M+2,−(M+3)
and reports worse averages than its two-giant variant. This is a scoped prior
negative, not a rejection of its signed version or every shifted design.
Worst-case memory/fallback must match; identical square-root order alone is
not an equal-memory experiment. Treat the raw2.7 tail claim cautiously until
its precise scope is reproduced for the selected finite schedule.

The raw review's small-prime test cannot settle a reported32-bit discrepancy;
its speculation of a setup artifact and numerical range are not accepted
uncertainty estimates. Likewise, paired candidate enumeration costs many RAM
events per pair, not one; the proposed1M-event design count is not a certified
budget. No universal novelty, attainability or lower-bound claim is adopted.
