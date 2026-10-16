# Original scope — fresh analytic discovery r9

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

Status at fixation: DISCOVERY / UNRESOLVED. Campaign remains 4/10. This is
new research, not an appeal or modification of F. F, its reviews and all parent
corrections are preserved unchanged as private historical inputs. No result
acceptance, manuscript, formalization, nested worker or external release here.
Only this r9 directory is writable. Parent integrates.

## Initial screen and choice

The initial lane is retained after a bounded screen of the exact FK source,
its three walk/spectral companions, Fill–Janson subtree-power asymptotics,
Abraham–Delmas–Nassif global additive measures, Croydon resistance-space
convergence, Croydon–Hambly–Kumagai heavy conductances, Andriopoulos tree
potentials, and Archer decorated trees. No directly applicable all-edge
barrier spectral theorem has been identified. This is not a novelty verdict.
The known additive-measure results already pay important geometric operations;
the target must include, and pay, interacting stable cuts and every cyclic
block with only the actual second offspring moment.

## Frozen full target G (before proof attempt)

Fix EVERY real q>4 and EVERY alpha in (1/2,1). For EVERY integer n>=1 sample
(M_n,A_n) with n edges and probability proportional to
q^{k_M(A)+(|A|-|V(M)|)/2}. Retain all loops and parallel edges. Independently
put iid R_e on EVERY edge, P(R_e>r)=r^{-alpha} for r>=1. Use original degree
m(v)=deg_M(v), including two loop darts, and the generator

 L_n f(v)=m(v)^{-1} sum_{nonloop e=vw} R_e^{-1}(f(w)-f(v)).

Let K_n=(-L_n)^{-1} on degree-mean-zero functions, zero in the one-vertex
case. Put N=2n+1 and b_N=N^{1/(2alpha)}. For the exact marked corner tree,
list its nonroot nodes in preorder; each corresponds to a parent-block
corner and thus to one original dart. Assign its pole to the corresponding
one of N-1 equal cells of [0,1]. This defines an isometry U_n from
L²(m/(2n)) to L²[0,1]. Extend U_n K_n U_n* by zero on the orthogonal
complement, and restrict to H0={f in L²[0,1]: integral f=0}.

Let e be the source-normalized Brownian excursion and (T_e,d_e,mu_e) its
rooted Brownian CRT. Let ell be skeleton length (d_e on each arc). For
ell-a.e. x, let I_x be the open interval in [0,1] coding the component
above x away from the root; write s_x=|I_x| and u_x=1_{I_x}-s_x in H0.
Use the EXACT source offspring law (block:offspring), p_2=P(xi=2) and
sigma²=Var(xi) in (0,infinity). Conditional on e, let P be a Poisson
measure on skeleton x times r>0 with intensity

 (p_2/sigma) ell(dx) alpha r^{-alpha-1} dr.

Define the candidate limiting operator by the positive series

 K_e,alpha=sum_{(x,r) in P} r (u_x tensor u_x) on H0,
 (u tensor u)f=u integral u f.

The FULL assertion G is joint convergence, through ALL integer n,

 (sigma H_N/(2sqrt N), [2n b_N]^{-1} U_n K_n U_n*)
       => (e,K_e,alpha)

in C[0,1] times trace norm on the self-adjoint trace-class operators on H0.
H_N is the source's linearly interpolated preorder height process with
H_N(1)=0. The same e must occur in the operator construction.

As part of G, not an assumed construction, prove that K_e,alpha is a.s.
well-defined, positive trace class, nonzero and injective on H0. Give the
self-adjoint inverse A=K_e,alpha^{-1} with domain Ran(K_e,alpha), and its
closed quadratic form with domain Ran(K_e,alpha^{1/2}). Prove its top
inverse eigenvalue is finite, strictly positive and nonconstant. In particular,
with tau_n=||K_n||,

 n^{-[1+1/(2alpha)]} tau_n
       => 2^{1+1/(2alpha)} ||K_e,alpha||.

All constants and interval/degree normalizations are part of the target.
No largest-single-bridge identification or Frechet law is asserted. No
resistance-metric compactness or process-path limit is included.

NO added offspring moment, bounded blocks, tree-only model, bridge-only
disorder, changed clock, restricted q, reduced alpha range, subsequence,
conditional localization or endpoint alpha=1/2 may replace G. If any full
bridge is unpaid, report G UNRESOLVED; supporting deductions do not replace
it. All earlier campaign vetoes remain in force.
