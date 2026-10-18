# T332 continuation: finite coupling checkpoint

Author-side work by Myeongjin Kang, no affiliation. Original prose CC BY 4.0. No nomination, no independent gate, no acceptance claim. The full target is copied verbatim in original-scope.txt. This round continues the unresolved target, with explicit authorization; it is not a new source family or renamed result.

## Verified conditional interface

The copied parent-coupling-note.md is author-side assistance, credited to the parent, not independent review. I checked its finite proof against source332 main.tex lines70–200 and480–648. The lift v_i(omega,e)=lambda_omega w_e 1_{X_i(omega) in T_e} has exactly the first expected distance as its ell-one norm. The source's specified output is the expected coordinate median of three independent index samples from G_i. On each fixed omega, all rooted cuts of the median agree with a single actual tree vertex. Thus averaging over omega gives probabilities and contracts ell-one distances back to W1. The source estimate is applied BEFORE the omega average; it squares E d and does not substitute E d². No gap found in that conditional finite lemma.

## Exact weaker sufficient coupling objective

For B=(1/t) sum_{s=1}^t A^s and b_ij=pi_i B_ij, the identical proof only requires a joint coupling with

    sum_ij b_ij (E d(X_i,X_j))² <= K² sum_ij b_ij W1(mu_i,mu_j)².

It does not require an individual pair bound. With this hypothesis the cotype constant is sqrt(3024) K. This is a sufficient interface only. A uniform K over all finite weighted label trees, all reversible A, all stationary pi, all t and all marginal families has not been proved. At t=1 cotype itself is trivial by taking nu_i=mu_i, so a difficulty in this stronger coupling objective at t=1 need not obstruct cotype.

## Direct feasible scalar smoothing fails the constant-family test

Let q_i(e)=mu_i(T_e), h_i(e)=sum_j G_ij q_j(e), and phi(s)=3s²−2s³. The h_i satisfy all probability-flow constraints. For a,b>=0 and a+b<=1,

    phi(a+b)−phi(a)−phi(b)=6ab(1−a−b)>=0.

Consequently applying phi to each h_i also satisfies the flow inequalities and the root budget. This provides a formally feasible smoothing, unlike the source's layerwise phi reconstruction. It does NOT prove cotype: if every mu_i equals a common nonbinary measure, the right side of cotype is zero, while phi changes its cut masses. Already a two-vertex tree with mass1/4 at its leaf changes that mass to5/32. This route therefore fails even before estimates. It does not rule out a calibrated or coupled smoothing.

## Primary operations checked so far

Li–Anantharam arXiv1908.01388v2 PDF downloaded into private/li-anth.pdf; pdftotext -layout produces private/li-anth.txt. Read text lines300–420 (definition2 and theorem4 hypotheses),620–705 (statements15–18),2620–2690 (§5.4 complete proof17 and16),5980–6085 (AppendixJ complete proof18),6080–6160 (references). Also initial HTML abstract/introduction lines0–95. Theorem17 uses equality of ultrametric balls when centers are closer than their radius, applied to arbitrarily small powers; it is not an arbitrary-tree argument. AppendixJ applies an FRT-type random tree to the INDEX metric W1(mu_i,mu_j), then glues pair couplings along that query tree. Its expected bound is23.1 log n. This is precisely the index/label distinction retained in the parent note. General finite metric and snowflake estimates likewise do not give an absolute weighted-tree bound. Full proof of theorem4 and most other portions remain unread.

## Current unpaid problem

Construct a universal first-cost simultaneous coupling on arbitrary finite weighted label trees, or prove the weighted squared-first-cost interface above directly for the source's Cesaro kernels, or replace it by an actual feasible cotype construction. No claim of nonexistence follows from the failure of direct phi smoothing or the lack of a result in the primary passages read.
