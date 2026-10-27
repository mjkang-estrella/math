# An alternative to explicit cyclic Jacobi compression — not yet formalized

The parent has proved the full classical root-distribution theorem for Jacobi
matrices with a finite arbitrary Jacobi head and an eventual free path. This
file records a potentially shorter route for the still-unproved source bridge.
It is a mathematical implementation note, not acceptance or discovery credit.

Let H_s be a real symmetric matrix obtained from a fixed finite symmetric head
by appending s path vertices at one distinguished coordinate, with unit coupling
and zero new diagonal. Let h_s = det(xI-H_s). Suppose a fixed nonzero monic F
and monic p_s satisfy h_s = F p_s and every consecutive p_s,p_(s+1) is coprime.
These must eventually be derived from the source's actual mixed Gram matrices;
they must not be silently assumed as a source theorem.

1. Principal-submatrix spectral counts give, for every real t and each sign,
   0 <= N_(s+1)^±(t)-N_s^±(t) <= 1. The parent has formalized the needed
   generic count tools, although their application to a general head family
   and the multiplicity calculation below are still pending.
2. Since dim H_(s+1) = dim H_s + 1 and all eigenvalues are real,
   m_(s+1)(t)-m_s(t) = 1 - ΔN^+(t) - ΔN^-(t), hence lies in {-1,0,1}.
3. If t is a root of p_s, coprimality forces it not to be a root of p_(s+1).
   The common F cancels exactly in multiplicities, so
   multiplicity_t(p_s) = m_s(t)-m_(s+1)(t) <= 1. All p_s split over R
   because they divide real-split characteristic polynomials. Thus p_s is
   squarefree. This uses no Lanczos basis and retains every multiplicity of F.
4. At s=-1 use the principal minor deleting the attaching coordinate from H_0.
   The border determinant gives h_1 = x h_0 - h_minor. Thus F divides h_minor,
   p_-1 = x p_0 - p_1 is its quotient, and p_-1,p_0 are coprime. The same
   multiplicity argument proves squarefreeness at this boundary. A nonempty
   attaching coordinate gives deg F <= dim H_0-1 through divisibility of the
   minor. This needs explicit proof, not a degree-zero shortcut.
5. The head-dimension bounds and monotonicity give eventual constancy of the
   exterior count of h_s. The root multiset identity roots(h_s)=roots(F)+roots(p_s)
   subtracts one FIXED exterior count, so the reduced counts stabilize too.
6. Head-vs-tail interval counts force roots of h_s in every open subinterval
   of (-2,2), as in the now-implemented Jacobi proof. To pass to p_s, shrink
   the target interval to avoid the finite real zero set of F. Continuity and
   F != 0 allow this; no coprimality of F with p_s is needed. Closure then gives
   density at both endpoints -2 and 2.

This could replace the explicit cyclic-compression construction while preserving
all source quantifiers. The remaining source obligations are unchanged: construct
the literal one-tail mixed Gram family for arbitrary Specht partitions; prove its
principal/path structure and fixed factorization; identify the source reduced
polynomials and boundary index. Generic head-family hypotheses alone do not
constitute a Lean proof of MathDB372352. The alternative has not had a separate
independent review and does not alter the accepted preliminary handproof.
