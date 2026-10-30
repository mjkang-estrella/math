# No qualifying discovery: exact current public obstruction

Research date: 2026-10-29 UTC (2026-10-28 America/Los_Angeles). Authority: research only. Credit nominated: zero. Counts remain 3/30 additional, 33/60 total.

## Retained full target and primary-source scope

The substantive target examined in depth is Gabrielov–Novikov–Shapiro, *Mystery of point charges*, arXiv math-ph/0409009, Conjecture 1.8, displayed equation (1.6), PDF page 6. For l points (a_i,b_i) and arbitrary real charges c_i, the source asks whether

F_alpha(x) = sum_i c_i ((x-a_i)^2+b_i^2)^(-alpha)

has at most 2l-1 real critical points for every alpha >= 1/2. Singular charge locations are outside the domain. The author-hosted manuscript at Purdue has the same numbering and statement on page 6; this is an author manuscript, not independently authenticated final publisher bytes. Recent papers call the corresponding published question Conjecture 1.9. These numbers must not be matched without checking the actual formula.

Catalogue selection: cached MathDB real-analysis-list.json, entry 376820. The entry is not evidence of openness. Source and current proof bodies were checked before a new formal or substantial proof investment.

The literal source permits cancellation giving a constant zero restriction. That is a domain/degeneracy correction, explicitly excluded from credit. The intended nonconstant statement is already publicly proved, too; this lane does not use the defect as a discovery.

## Decisive positive public evidence

1. Goncalo Oliveira, *Critical points of point charge potentials along lines*, arXiv:2609.00336v1, submitted 2026-08-31 20:29:27 UTC. Actual full nine-page body read, including Theorems 1/2, Lemmas 1/2 and Propositions 1–3. Theorem 1 proves the full signed-charge bound for every p>0 after profile reduction. Theorem 2 supplies a stronger paired-function zero bound.
2. Xiuqing Duan, *Critical Points of Line Restrictions of Signed Point-Charge Potentials*, arXiv:2608.28376v2, PDF header 28 September 2026, internal date September 29. Actual definition and Theorems 2.1/2.3 read; abstract and introduction are not the sole evidence. Theorem 2.1 gives precisely the full reduced signed dichotomy for all alpha>0, including one global distinct-point bound with effective poles and multiplicity in the smooth case. I did not independently audit the entire projective-convexity proof.

Both precede this research. No absence-of-prior claim or worldwide priority conclusion is necessary: one matching positive public theorem suffices. These are public mathematical proofs, not a claim that their Lean certificates were replayed here.

## Exact all-parameter subsumption bridge

Take the target a_i=x_i and height h_i=|y_i|. Group indices with the same pair (a_i,h_i); add their charges and delete zero sums. Write the remaining m profiles as R_j(x)=(x-a_j)^2+h_j^2 with charge C_j != 0. Then m<=l and the original domain D_orig is a subset of the reduced domain D_red; cancellation may fill punctures only in the reduced formula. Equality of the potentials and their derivatives holds on D_orig.

If m=0, the restriction is zero on D_orig, a case treated explicitly by Duan. If m>=1, set p=2alpha>0. Then

F_alpha'(x) = -p sum_j C_j (x-a_j) R_j(x)^(-(p+2)/2).

This belongs to Oliveira's full paired space with generators R_j^(-(p+2)/2) and (x-a_j)R_j^(-(p+2)/2). His Theorem 2 gives at most 2m-1 distinct zeros on D_red. Restriction to D_orig and m<=l give exactly the intended source bound. There are no charge-sign, total-charge, separation, nondegeneracy or upper-exponent restrictions to bridge. Alternatively Duan Theorem 2.1 applies directly without changing exponent notation. Singular components are counted globally, not by multiplying the bound by their number.

This is the strongest actual generic-subsumption bridge found: not just a fixed-exponent case or a theorem about positive charges. A source-level Lean development would re-formalize the already public full result and earns zero.

## Independent examination of Oliveira's proof mechanism

Suppose an evaluation matrix of the paired space at 2m distinct real nodes were singular. A nonzero vector in its transpose kernel gives an auxiliary planar collinear potential U(a,b)=sum_r q_r((a-x_r)^2+b^2)^(-p/2), with k<=2m nonzero charges. Its two annihilation equations force critical points at (a_j,+/-h_j). For h_j=0 they force a critical point with vanishing Hessian, since U_aa=p(p+1)sum q_r|a_j-x_r|^(-p-2), U_bb=-p sum q_r|a_j-x_r|^(-p-2), and U_ab=0.

Direct differentiation gives U_aa+U_bb+(p/b)U_b=0 away from the axis, extending analytically across it. Consequently every nondegenerate critical point is a saddle. For a critical point whose first nonconstant Taylor term has degree d, the local gradient degree is 1-d; on the axis the homogeneous polynomial coefficients satisfy

(d-2j)(d-2j-1)c_j + (2j+2)(2j+1+p)c_(j+1)=0.

The ordinary ODE uniqueness and p-homotopy argument in Lemma 1 makes its gradient nonzero on the unit circle. A small Morse perturbation therefore preserves at least one saddle off-axis, or at least two at a Hessian-zero axis point. Sard's theorem supplies the perturbation while keeping all k charges and making total charge nonzero. This produces at least 2m saddles.

At infinity the normalized gradient has degree +1. Each deleted charge disk contributes -1 with induced boundary orientation, regardless of the charge sign. The sum is 1-k. Each saddle contributes -1, so the perturbed auxiliary potential has exactly k-1<=2m-1 critical points, a contradiction. This addresses the otherwise serious objection that cancellation/zero total charge or singular profiles might invalidate a naïve Morse count. The perturbation, not a sign assumption, handles the zero total charge.

This is a read-and-derived proof dependency check, not an independently formalized replacement for degree theory, Sard, analytic continuation, or local ODE uniqueness. Six exact sample determinants and four Sturm counts in check.py are finite diagnostics only. They cannot prove the paired theorem.

## Distinct earlier lead: Castle radius formula

Paul Castle, arXiv:1801.09904v1, Conjecture 1.2, equations (1.2)/(1.3), pages 3 and 13–14 were read. Nonzero complex t_i,p_i define the inverse germ of f(z)=z exp(z) product_i(z-t_i)^(p_i), with local branches at zero. The conjectured radius uses a solution phi to

(1-S)(p_i+phi_i)+t_i phi_i=0, S=sum phi_i,

and integer phases exp(2pi i sum l_i phi_i). Away from exceptional denominators put z=S-1 and phi_i=z p_i/(t_i-z). Summing gives exactly 1+1/z+sum_i p_i/(z-t_i)=0, the ordinary critical-point equation. Thus a corrected radius claim has an immediate inverse-singularity bridge, but still needs global sheet accessibility and exclusion of competing singularities for all complex parameters.

The printed formula already fails by an exponential normalization in the perfectly regular m=1,p=t=1 case. Let r=(sqrt(5)-1)/2 and phi_+=1+r, phi_-=-r. The inverse radius is R=r(1-r)e^r. To see this without coefficient numerics, use g(z)=-f(z)=z(1-z)e^z=z-H(z), where H has nonnegative coefficients, H'(s)<1 for 0<=s<r and H'(r)=1. For any such s the fixed-point map z -> w+H(z) contracts the disk |z|<=s when |w|<s-H(s). The inverse is holomorphic up to R. At R the real inverse approaches r while g'(r)=0; an analytic inverse at R would contradict differentiating g(g^-1(w))=w. Hence the radius is exactly R.

For real p=t=1 all integer phase factors have unit modulus. The printed two possible values are B_+=e^(-phi_+)R<R and B_-=e^r M>M, where M=|( -1-r)(-2-r)e^(-1-r)|. In fact M/R=phi_+^6 exp(-sqrt(5))>1: log u>2(u-1)/(u+1) for u>1 and 12(phi_+-1)/(phi_++1)>sqrt(5), the latter equivalent to 9sqrt(5)>17. Thus neither printed value is R. The missing exp(S) factor explains this case directly. This is explicitly classified as a normalization correction, zero credit, not a substantive new source-conjecture resolution. No global corrected complex-parameter theorem is asserted.

The closest current companion read was Neto, EJDE 2025/90, Theorem 8.1 and Corollary 8.2. Its radius derivation replaces n-dependent expressions inside coefficient extraction by pointwise asymptotics. Such substitution does not control coefficients whose index also tends to infinity. I do not rely on it to clear or prove Castle's corrected full question. No assertion of an independently verified all-complex subsumption by Neto is made.

## Other capped leads and access limits

The McKay catalogue lead was dropped on identifying the source as Gaunt–Merkle, within the user's excluded Gaunt scope; no attack. Cached Matkowski exclusions were reconciled; the actual source Corollary 1 publicly supplies counterexamples, so no investment. Micheas2508.04760v2 Conjecture 3 is directly solved by choosing gamma=1 and u_n=a_n b^n+c_n d^n; moreover the source itself prints a proof. No credit.

Duan2609.09637 Theorem1.1 concerns the Voronoi-cell-count conjecture with the same historical numbering, not the line bound; actual formula and scope checked. It supplies no contradiction to Oliveira or Duan2608.28376.

No further target selection after this capped screen. The concrete outcome is a full-source public-subsumption exclusion plus a precise, uncredited normalization obstruction for a distinct lead. No fresh eligible full question survived this screen. No complete ordinary discovery candidate, no PROOF.md, no Lean work, no acceptance recommendation.

Registry coverage used the recent complete r7 D5 and Problems trees and head receipts, plus count registry and OpenAI preprints tree. Targeted path/string search found no relevant point-charge/Castle proof there; this absence did not clear novelty and was superseded by positive current arXiv bodies. No new GitHub API traversal. Search results are leads only; primary PDFs carry the conclusions. All direct fetches succeeded, no 403/429/challenge encountered in this lane. Earlier mathdb.com and api.github.com limits were respected by making no requests to those hosts. Unknown work outside this bounded screen remains unknown.
