# H013 explicit group-action features: three scoped screens

2026-10-08. Native Sol independent mechanism followup; root checked formulas.
No prototype/experiment, new Lean claim or validated gain. These are specific
constructions, not a universal impossibility for learning. H=F_q^*, P=nG!=O,
c_chi(f)=E_H f(nG)*conj chi(n); all scalar actions/phase costs are paid.

1. **Weighted dilation averaging.** Freeze a cheap seed g, e.g. a hash-to-four-
   phases function, and multipliers u_j. Put f_T(P)=T^-1 sum_j conj chi(u_j)*
   g(u_jP). Exact substitution gives c_chi(f_T)=c_chi(g). For iid uniform u_j,
   E||f_T-c_chi(g)chi||_2^2=(||g||_2^2-|c_chi(g)|^2)/T. It suppresses other
   components but does not create absolute target correlation. Each inference
   pays T views; an outer correlation estimator expands into the same paid seed
   views at u_j*c. Full-group averaging costs q-1 views. A compressed evaluator
   or effective distillation is an additional missing primitive, not free
   equivariance. No need to build this filter before finding a correlated seed.

2. **Labelled landmarks.** Store L known-log A_i=a_iG, scan J fixed nonzero
   dilations u_j of P, and return conj chi(u_j)*chi(a_i) on a hit or0 otherwise.
   V={u_j^-1 A_i} has size<=LJ, and f(nG)=chi(n)1_V(nG), so c=|V|/(q-1)
   and ||f||^2=|V|/(q-1). A hit also recovers the FULL scalar a_i/u_j. With
   independent uniform rerandomization and the frozen complete scan, expected
   lookups J(q-1)/|V|>=(q-1)/L. Paid setup L gives the square-root tradeoff
   L+q/L even before scalar/character/verification work. Precomputing V just
   creates a larger paid dictionary. Interpolation outside V was not supplied.

3. **Subgroup orbit canonicalization.** For K=<u> of size h, enumerate the
   whole K orbit and choose the unique minimum under a fixed encoding order.
   If C(P)=v_P P, define f_K(P)=conj chi(v_P). It satisfies f_K(vP)=chi(v)f_K(P)
   for v in K, at h paid views per inference. If t=(q-1)/h and n_C denotes the
   scalar of each canonical representative, c_chi=t^-1 sum_C conj chi(n_C).
   Within-coset alignment supplies no alignment across cosets. Proper K has
   lambda_K=1 because a nontrivial character trivial on K exists; local zero
   defect cannot certify global correlation. If K subset kerchi the feature
   is1 and its nontrivial coefficient0. Full K=H gives magnitude1 but pays q-1
   views. Under an explicitly ideal independent random-rank model with chi|K
   nontrivial, E|c|^2=1/t; this is not a theorem for a fixed hash or learned order.

An exact SMALL full-group equivariant frame is itself an ECDLP primitive:
if A(nG)=n^-1 A(G) with explicit scalar multipliers, choose v in A(P), compute
vP and compare against the paid points aG for a in A(G). A match reveals n=a/v.
This does not apply to approximate or character-only equivariance, nor prove
cheap exact frames impossible. It identifies what cannot be assumed for free.

Generic averaging/canonicalization are established mechanisms; primary leads
are [Frame Averaging](https://arxiv.org/abs/2110.03336) and
[Canonicalization Perspective](https://arxiv.org/abs/2405.18378). No novelty or
ECDLP guarantee is attributed to either learning paper. The useful conditional
exponent/memory calculation is retained in H014-preflight-disposition.md.
