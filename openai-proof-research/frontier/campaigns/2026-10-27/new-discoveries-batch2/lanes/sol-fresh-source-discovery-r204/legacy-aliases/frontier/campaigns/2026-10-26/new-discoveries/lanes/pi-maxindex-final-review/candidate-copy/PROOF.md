# Sharp maximal index in every dimension d≥5

Status: **candidate, credit0**. The universal bound and uniform sharpness construction below are completely formalized in12Lean modules. The final theorem classifies EVERY index0≤k≤d² for EVERY dimensiond≥5 using actual independently sorted arrays and the full probability simplex. Source/math/serious novelty review is pending; no acceptance or absolute priority claim. Very small dimensions remain separate research notes and are not claimed by this candidate's classification.

## Source

Caro–Graswald, *Necessary Criteria for Markovian Divisibility of Linear Maps*, arXiv2009.06666v3, actual Conjecture4.19p18 and preceding Remark4.18 read. Source defines separately sorted top-k sums A_k of a_ij=(p_i+p_j)/2 and G_k of g_ij=sqrt(p_i p_j), for a nonnegative probability vector p∈R^d. It claims maximal h(d)=2d−5. PDF in sources/2009.06666v3.pdf. The main theorem below proves the exact claimed maximal index for ALL d≥5. Very small dimensions need separate treatment and are not the basis of a discovery claim. The preliminary reviewer read the actual published2021body embedded in Caro’s thesis and confirmed the same conjecture; full-body citing-corpus review remains required.

## General finite-entry facts

Let k=2m+1, m≥0, and n≥2. Consider any k-element set S of ordered pairs. Define
c_i=(#{j:(i,j)∈S}+#{j:(j,i)∈S})/2.
Then Σ_(ij∈S)a_ij=Σ_i c_i p_i, each c_i≥0, each c_i≤(k+1)/2=m+1, and for distinct i,j,
c_i+c_j≤(k+4)/2=m+5/2.
Proof: relative to one distinguished vertex, a selected loop contributes1 and every other incident ordered edge contributes1/2, so c_i≤k/2+1/2. Relative to two vertices, at most4ordered pairs are internal and contribute1 to c_i+c_j, other pairs contribute at most1/2; hence pairboundk/2+2. No symmetry of the selected mask or tie convention is assumed.

Let a=max c_i, choose its vertexu, let b=max_(i≠u)c_i, and let p=max p_i. Then
Σ_i c_i p_i≤a p_u+b(1−p_u)≤a p+b(1−p).
If p≤2/3, this is at most(2a+b)/3=(a+(a+b))/3≤(4m+7)/6. This applies to EVERY arithmetic mask, hence to A_k.

For geometric entries, Σ_(allij)g_ij²=(Σp_i)²=1. Thus G_k≤sqrt(k) by Cauchy. More sharply, g_uu=p is a largest entry; a maximizing k-element set can be chosen to contain it, even if ties occur. Therefore
G_k≤p+sqrt((k−1)(1−p²))=p+sqrt(2m(1−p²)).
The largest-entry replacement and exact distinct-index cardinality are proved in FiniteSelections.lean. SortedBridge.lean proves the literal sorted-take sum equals the finite-mask maximum.

## Universal sufficiency

If p≤2/3, then
A_k+G_k≤(4m+7)/6+sqrt(2m+1)<m+3.
The strict final inequality follows by squaring the positive right-hand margin:
(2m+11)²−36(2m+1)=4m²−28m+85=(2m−7)²+36>0.

If p>2/3, let u be a maximum-probability vertex and ε=1−p. Every arithmetic entry outside row/columnu is≤ε<p/2. For ANY k-element mask, bound each entry by baselinep/2 plus the following nonnegative extras: the(u,u)entry has extra p/2, and a(u,i)or(i,u)entry has extra p_i/2. All other entries need no extras. Summing, the distinguished loop appears at mostonce and each tailp_i at mosttwice, yielding
A_k≤(k+1)p/2+ε=1+mp.
Combined with the sharper geometric bound,
A_k+G_k≤1+(m+1)p+sqrt(2m)*sqrt(1−p²)
≤1+sqrt((m+1)²+2m)=1+sqrt(m²+4m+1)<m+3.
The middle step is ordinary two-dimensional Cauchy; the final gap follows from(m+2)²−(m²+4m+1)=3>0. No numerical optimization enters the proof.

Set m=d−3. For every d≥3, the source index k=2d−5=2m+1 is positive and the universal top-sum bound is STRICTLY less than d.

## Explicit uniform sharpness family (d≥5)

Let m=d−3≥2. Use the probability vector
p=(4m²,1,...,1,0,0)/(4m²+m), with exactly m copies of1.
Thus sqrt-probabilities are proportional to(2m,1^m,0,0). At the next indexk′=2m+2=2d−4, select for A: distinguished diagonal, both distinguished-to-positive-tail orientations(2m entries), and one distinguished-to-zero entry. Select for G: distinguished diagonal, both distinguished-to-positive-tail orientations, and one positive-tail diagonal. These are two genuine k′-element sets of ordered pairs. Since the actual top sums dominate ANY such selections,
A_(k′)+G_(k′) is at least the sum of the following exact selected sums:
A_selected=((m+3/2)r²+m)/(r²+m),
G_selected=(r²+2mr+1)/(r²+m), r=2m.
Consequently
A_selected+G_selected−(m+3)
=[−r²/2+2mr−m²−2m+1]/(r²+m)
=(m−1)²/(4m²+m)>0.
For example d5,m2 gives p=(16,1,1,0,0)/18, A_selected=29/9,G_selected=11/6,total91/18>5.
Hence no index larger than2d−5 can hold universally (top sums are nondecreasing in k), and the claimed maximal h(d)=2d−5 is established for every d≥5.


## Formal endpoint

`MaxIndex.source_index_classification` states: for every d≥5 and every k≤d², the inequality holds universally over nonnegative p:Fin d→R with sum1 if and only if k≤2d−5. `source_universal_index` proves the strict bound at2d−5 for d≥3; `source_next_index_counterexample` constructs an actual probability vector on Fin d violating the next index for d≥5. The finite-mask/sorted-array bridge, geometric normalization, maximum inclusion with ties, incidence constraints, row/column extras, mask sizes/sums, index reparameterization and monotonicity are all proved. No combinatorial, analytic or numerical certificate is left as a residual premise. Numerical scripts are supporting evidence only.

Remaining gates: serious independent source/current-published/prior-art review; independent strict Lean review; paper with rendered visual QA; exact proof packet and fresh extracted strict replay. Count remains0 for this candidate.
