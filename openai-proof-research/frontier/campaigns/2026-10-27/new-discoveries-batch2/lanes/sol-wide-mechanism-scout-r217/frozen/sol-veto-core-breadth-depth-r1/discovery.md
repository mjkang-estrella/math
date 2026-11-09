# Main discovery proposal

The complete statement, proof, public sharpness construction, quantifiers and
source comparison are in PROOF.md. The key refinement to Berger's plurality
coupling keeps the whole comparison-candidate column and the first-choice
voters' cost instead of aggregating both into an unrestricted residual bucket.

For mu=1/S, p=plu(b)/n, q=q(b), K=mu(1-p)+q, H the average distance cost
of voters ranking b first, and D=d(a,b), the three decisive estimates are

    excess <= 2mu(R-H)+(1-K)D,
    (1+mu)R-mu H >= KD/2,
    H >= D max(0,q+p-1)/2.

The score floor q>=[p+s_m(1-p)]/S yields the target through a two-case
identity at p=(S-s_m)/(S-s_m+1). This covers m=3 symbolically with
s=(1,u,v), all 0<=v<=u<=1, and extends unchanged to arbitrary m.

An early floor-only attempt discarded H and worked only when
p<=(S-s_m)/(S-s_m+1). Rather than stopping after finite tests, the high-p
case was resolved by the special-flow intersection bound. The source's lower
construction lies exactly at this split, explaining the sharpness.

No new credit is claimed for sm=0, proportional or k-approval subcases,
weighted Hall, plurality transport, exact arithmetic controls, formalization,
or the already-public lower bound. Independent review must examine the full
ordinary proof and novelty limits before any acceptance decision.
