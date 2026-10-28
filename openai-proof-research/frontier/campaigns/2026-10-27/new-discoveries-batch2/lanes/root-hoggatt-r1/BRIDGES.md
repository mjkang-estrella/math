# Formal handoff: exact remaining obligations

This is a precise proof-porting map, NOT a certificate of the Hoggatt theorem.
`formal/ResidueBridge.lean` checks three small lemmas with pinned Lean 4.34.1
and the requested mathlib commit. The checker reports only propext,
Classical.choice, Quot.sound. Run `python formal/replay.py` from any directory.
No unproved declaration or assumed theorem is inserted into that file.

## Intended definitions

Work with `Polynomial ℝ`. For q>1 set QI(q,j)=sum_{i<j}q^i and
QFac(q,n)=prod_{j=1}^n QI(q,j). Define QB(q,N,k)=0 if N<k and otherwise
QFac(q,N)/(QFac(q,k)*QFac(q,N-k)). Set

    F(q,N,m) = sum_{k=0}^{N-m+1}
      C(q^(m*(k*(k+1)/2)) * prod_{j<m} QB(q,N,k+j)) * X^k

only under 1<=m and m-1<=N. Define the q derivative coefficientwise:
coeff(Dq(q,f),k)=QI(q,k+1)*coeff(f,k+1). Ordinary Hadamard multiplication
has coeff(f star g,k)=coeff(f,k)*coeff(g,k).

A finite ordered root certificate for degree d is a strictly increasing
map r:Fin d→ℝ, all r_i<0, and f= C(lc f)*prod_i(X-C(r_i)), lc f>0.
Strict q-separation adds r_i/q<r_(i+1). Weak interlacing of g,f requires
certified real root multisets of degrees d-1,d, ordered nondescending,
and r_i<=s_i<=r_(i+1). Strict replaces the inequalities by <.
Equal-degree left alternation requires s_i<=r_i and r_i<=s_(i+1).
Constants use empty root vectors; constant/linear interlacing is vacuous.

## Obligations, in dependency order

1. QB positivity in range, Gaussian step
   QI(q,k+1)*QB(q,N,k+1)=QI(q,N)*QB(q,N-1,k), and finite q-binomial
   identity F(q,N,1)=prod_{j=1}^N(1+C(q^j)*X). Prove by finite products
   and induction, checking boundary N=m separately.
2. Formalize Garloff–Wagner Theorem 4 (1996), including part (c)'s exact
   exceptions. It is a published mathematical dependency, NOT available as
   an assumed Lean axiom. Prove/import a checked proof. This is likely the
   largest missing library development. Alternatively replace it with a
   fully proved total-positivity or stability argument with the same scope.
3. Derive consequences A and B from PROOF.md, including degrees and nonzero
   constant coefficients. B uses f=P(qX),g=P,p=R,q=R in the classical
   theorem. Nonproportionality follows from P_0>0,deg P>=1 and q>1.
4. Dq evaluation identity at x!=0 and degree d-1. Formalize the endpoint
   signs in q-Rolle; apply polynomial continuity and IVT in d-1 disjoint
   intervals. Degree count gives all roots, no multiplicities. The strict
   separation propagation is `separation_from_brackets` in the initial file.
5. Partial fractions for deg g=d-1 and squarefree f:
   g/f=sum_i (g(r_i)/f'(r_i))/(X-r_i), with c_i>=0 and sum c_i>0.
   This can be proved by Lagrange interpolation, avoiding rational-function
   limits. Positivity of sum follows by comparing leading coefficients.
6. At each Dq f root y, show y and qy lie in the same gap, hence the residue
   denominator products are positive. `same_gap_product_pos` checks that
   elementary order fact. `residue_q_difference` checks the exact algebraic
   divided-difference identity for each summand. Sum it to obtain (2).
   IVT plus degree d-2 proves strict interlacing of Dq g,Dq f. Handle d=2
   as constant/linear, not by a nonexistent root index.
7. Coefficient extensionality proves (3):
   Dq(F(q,N,1) star F(q,N-1,m-1))
      = C(QI(q,N)*q^m)*F(q,N-1,m).comp(C(q^m)*X).
   All finite-support and out-of-range coefficient cases must be discharged.
8. Induct on m, starting with weak interlacing at m=1. For each N>=m use
   (2)-(7) to get strict interlacing of F(q,N-1,m),F(q,N,m). Positive argument
   scaling q^m preserves the order and multiplicities of roots.
9. State the endpoint in terms of the source's boxed plane partitions,
   prove their finite weighted enumeration is MacMahon's product, and
   prove normalization (1). A certificate only for F without that literal
   bridge does not establish the source statement. Source q=1 case needs a
   checked proof too (e.g. the original derivative induction). Restricting
   the new q>1 theorem to integer q>=2 is immediate once established.

## Exact current gap

The written mathematical argument has no identified missing inference.
The literal source theorem is not formalized: obligations 1-9 above remain
apart from the three explicitly checked elementary lemmas. In particular,
there is no claimed strict replay of the full endpoint, no independent
adversarial review, and no completed paper artifact. These are acceptance
requirements for root, not credits earned by this research handoff.
