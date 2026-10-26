# Sharp maximal index in every dimension d≥5: proposed general proof

Status: **research candidate, credit0**. The proposed uniform large-dimension theorem is now completely formalized in12Lean modules (76declarations). A fresh strict isolated replay passed with Lean4.34.1, warningsAsError and only the three standard axioms. All76declaration types were inspected. Actual independently sorted arrays, combinatorial/normalization bridges and the uniform sharpness family are proved, with no residual mask/counting hypotheses. See candidates/maximal-index for the three-page rendered manuscript and full certificate. Preliminary independent math/source review PASS; full-body citing/nearest-prior coverage, independent complete formal/manuscript review and extracted packet remain pending. Small-dimensional classification below remains research-only and is not claimed by the manuscript's formal maximality theorem. One substantive uniform d≥5 outcome is proposed, never helpers or scans.

## Source

Caro–Graswald, *Necessary Criteria for Markovian Divisibility of Linear Maps*, arXiv2009.06666v3, actual Conjecture4.19p18 and preceding Remark4.18 read. Source defines separately sorted top-k sums A_k of a_ij=(p_i+p_j)/2 and G_k of g_ij=sqrt(p_i p_j), for a nonnegative probability vector p∈R^d. It claims maximal h(d)=2d−5. PDF in sources/2009.06666v3.pdf. Main theorem proposed below proves the exact claimed maximal index for ALL d≥5. Very small dimensions need separate treatment and are not the basis of a discovery claim. Independent preliminary reviewer confirmed the same conjecture in the actual published2021body embedded in Caro’s thesis; full-body citing-corpus review still required.

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
The replacement argument to include a largest entry and the distinct-index cardinality must be proved formally; not left as a source bridge assumption.

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

## Small dimensions: proposed complete classification

These cases support a full answer but are NOT separate discoveries or the basis of the novelty claim. Proposed exact classification:
h(1)=0,h(2)=1,h(3)=2,h(4)=4,h(d)=2d−5 for d≥5.

Let probabilities be sorted p1≥p2≥p3≥p4, and write xi=sqrt(pi).
- Top1 A+G=2p1≤2. At d1 the sole positive index1gives2>1, so only0works.
- Top2 A+G=(5/2)p1+(1/2)p2+x1x2≤3p1+p2≤3. This gives d3index2. At p=(4/5,1/5), index2sum5/2>2, excluding index2for d2.
- For d3,p=(4/5,1/5,0), index3sum17/5>3.
- For d4,p=(4/5,1/5,0,0), index5sum22/5>4.
- Universal top4 bound≤4 for d4: sorting implies
  A4=2p1+p2+max(p2,(p1+p3)/2),
  G4=p1+2x1x2+max(p2,x1x3).
  These formulas follow because after the distinguished diagonal the next two entries are the two orientations of(1,2); the next is either(2,2)or a(1,3)orientation. Ties do not change the sum.
  The difference4−(A4+G4), using Σ_(1..4)pi=1, has one of four nonnegative expressions, according to the two chosen max branches:
  (i) bothp2: (x1−x2)²+4p3+4p4.
  (ii) arithmetic-star/geometricp2: (1/2)(x1−2x2)²+(7/2)p3+4p4.
  (iii) arithmeticp2/geometric-star: (1/2)(x1−2x2)²+(1/2)(x1−x3)²+(7/2)p3+4p4.
  (iv) bothstar: (1/3)(x1−3x2)²+(1/6)(x1−3x3)²+2p3+4p4.
  Check each by direct expansion; no branch constraint beyond choosing the maxima is needed for nonnegativity.

Thus the small cases can be certified separately and combined with the uniform d≥5proof. Any manuscript should lead with the substantive universal large-d result and describe small values plainly, rather than presenting a small-d wording counterexample as a discovery.

## Remaining gates

- Independently check every bound and the exact-source reading/current published form; delete any transcription scratch before candidate manuscript.
- Full serious prior-art search. Sourceopen label and local spectral searches do not certify novelty.
- Complete Lean proof using actual finite arrays/top-sum semantics. Mask cardinalities, largest-entry inclusion, row/column coefficient constraints, positive normalization/square-root bridge and sharpness-family sums cannot remain premises of the final endpoint.
- Independent adversarial review, paper, rendered PDF and extracted proof packet.

## Numerical exploration preceding proof (evidence only)

optimize_index.py alternates exact top-k mask selection in floating arithmetic and a leading-eigenvector update for x=sqrt(p).42starts each atd7,8,10,15,20,30,50,100: no violation at2d−5; violations at2d−4. The maximum found at oddk matches(d+sqrt(d²−8))/2, which is stronger than the proposed general bound but is NOT proved here. Numerical eigenvectors and that sharper numerical maximum receive no discovery credit.
