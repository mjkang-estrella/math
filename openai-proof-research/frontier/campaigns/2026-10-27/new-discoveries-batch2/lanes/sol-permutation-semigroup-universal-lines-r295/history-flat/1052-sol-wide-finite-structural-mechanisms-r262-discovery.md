# Sustained Schur route — precise gap, no discovery claimed

Target: Koutschan–Wong1904.01925v2 Conjecture1 p22. Exact quantifiers and source distinction are in SCOUTING.md. No PROOF.md is supplied because the ordinary source outcome is incomplete.

Let T_n={(x,y,x+floor(y/2)):1<=x,y<=n, x+floor(y/2)<=n}. These are ordered triples, including repeats. Write M(c) for their monochromatic count and C for a binary coloring. Total |T_n|=n²-floor(n²/4), by summing n-floor(y/2) over y.

## Mechanism A: exact quadratic reformulation, failed spectral certificate

For every triple, with signs s_i in {+1,-1}, its monochromatic indicator is (1+s_x s_y+s_x s_z+s_y s_z)/4. Form a symmetric zero-diagonal integer matrix W by adding one to each directed matrix entry for each unordered pair of distinct coordinate positions in each triple, retaining multiplicity. Let w_ij=W_ij for i<j. Repeated coordinate positions produce loops, omitted from W since they are never cut. Then

2M(c)=2|T_n|-sum_(i<j) w_ij [c_i != c_j].

For 1<=i<j<=n, direct enumeration of the coordinate-pair roles gives the universal explicit formula

w_ij=[i+floor(j/2)<=n]+[j+floor(i/2)<=n]+[2(j-i)<=n]+[2(j-i)+1<=n]+1+[i-floor(j/2)>=1].

The first two terms are the (x,y) roles, the next two the (x,z) roles, and the last two the (y,z) roles. Thus the conjecture is an exact maximum-cut bound for this structured matrix, not a finite-state conjecture alone.

For the source four-block sign vector s, the usual sufficient diagonal certificate would be Q=W-diag(s_i(Ws)_i) positive semidefinite. Indeed, for any sign vector t, t'Wt-s'Ws=t'Qt. This would prove M(t)>=M(s). It fails: at n=12 the exact integer vector

v=(22,-357,343,-319,-50,226,664,-172,-175,-62,-306,25)

satisfies v'Qv=-1021882. This is an exact disproof of that certificate, **not** a source counterexample: v is not a sign vector. The conjecture can hold despite the failed relaxation. No PSD inference relies on floating point.

The separate heuristic tries only final states after5 starts of12000 flip proposals at each n in {12,13,17,23,31,47,64,96,128,192}, with a source incumbent and deterministic RNG seeds. It found no final-state improvement. It does not certify maxima, exhaust the cube or even retain every intermediate improvement. The identity was also checked on25 random sign vectors per size. These are diagnostic checks only.

## Mechanism B: combinatorial triangle charging, a general obstruction

Any cut crosses at most two edges of a triangle. If weighted triangles can be packed under the capacities w_ij with total weight P, then cut<=sum w_ij-P, hence M>=|T_n|-(sum w_ij-P)/2. This is a distinct combinatorial charging proof template.

However, necessarily 3P<=sum w_ij. Count omitted loops exactly: x=z occurs n times (y=1); y=z occurs n times; x=y occurs floor((2n+1)/3) times. Multiplicities, including (1,1,1), are retained. Thus R=2n+floor((2n+1)/3) and sum w_ij=3|T_n|-R. Consequently even the best triangle packing can give a lower bound no larger than R/3, only linear in n. For n>=12 this cannot reach floor((n²+5)/6). This obstruction is universal and does not depend on a finite solver output.

Diagnostic fractional packing LPs at n=12,13,18,24,30 reach the capacity upper bound numerically. They are not exact certificates or proof of source minima. The first HiGHS invocation aborted with signal6; its empty stdout and stderr/guard record are retained. A second invocation explicitly restricted HiGHS to one thread under the *same caps* succeeded. No memory/CPU/wall cap was raised. The failure prompted a threading change, not access bypass or enlarged resources.

## Remaining parity route and exact missing inequality

Group y=2v and y=2v+1. With Y_v={2v,2v+1} intersect [1,n], exactly

M(c)=sum_(v=0..floor(n/2)) sum_(x=1..n-v) [c_x=c_(x+v)] sum_(y in Y_v)[c_x=c_y].

If an interior pair c_(2v),c_(2v+1) differs, its inner color sum is1. If it agrees, the inner sum is0 or2. This exposes information discarded by triangle packing and by integer-a predecessor arguments. v=0 contributes the number of vertices colored like c_1; no y=0 is introduced. The formula is a direct partition of the original triples; exact_checks.py independently exhausts all510 colorings for1<=n<=8 and validates the explicit weight formula at10660 entries for2<=n<=40.

The missing global inequality is that this parity-coupled sum is at least floor((n²+5)/6) for **every** binary coloring and every n>=12. No proof that adjacent pairs may be merged, that an optimal coloring has four intervals, or that local exchanges reach a global optimum has been established. An unrestricted compression can alter both the pair state and its appearances as x or x+v, so holding those roles fixed would be invalid. Next decisive step is an exchange/charging lemma accounting for all three roles and the n mod6 constants; adding more finite n is not that step.

Eligibility remains HOLD: the max-cut identity and triangle bound are elementary helpers, not substantive independent outcomes. The surviving parity route may be a routine extension of known pair-counting. Primary-body/current-registry/subsumption review must precede any claim of novelty. No accepted result or new-to-literature assertion is made.
