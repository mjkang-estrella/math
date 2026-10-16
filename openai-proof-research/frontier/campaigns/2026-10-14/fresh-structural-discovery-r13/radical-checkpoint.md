# Checkpoint 1: the exact torsion-free quotient operation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Fix the entire frozen TFS input and put U=(G*F_n)/N, N=<<w_1,...,w_m>>. The stipulated Theorem 1 embeds G in U. Define normal subgroups

T_0(U)=1,
T_{s+1}(U)=<< u in U : u^k in T_s(U) for some integer k>=1 >>_U,
T_omega(U)=union_{s>=0} T_s(U).

This is the standard torsion-free radical construction, not a new operation: Chiodo, arXiv:1107.1489v3, Definition 3.9 and Proposition 3.10, explicitly give it and identify it with the radical of Brodsky--Howie. We reproduce the proof to expose what still has to be established relative to the coefficients.

Every T_s is normal, the sequence increases, and its union is normal. If (u T_omega)^k=1 in U/T_omega, then u^k lies in some T_s, hence u lies in T_{s+1}. Thus U/T_omega is torsion free. If f:U->H has torsion-free target, induction gives T_s subset ker f: if u^k is in ker f, then f(u)^k=1 and f(u)=1; normal closure preserves this inclusion. The union is also in ker f. Consequently every torsion-free image factors through U/T_omega.

It follows, with no changed quantifiers, that TFS for this input is equivalent to

                     G intersect T_omega(U) = 1.             (R)

Indeed (R) makes U/T_omega the required torsion-free solution group. Conversely any torsion-free solution induces f:U->H injective on G and killing T_omega, forcing (R). Since the union is increasing, (R) is equivalent to G intersect T_s(U)=1 for EVERY finite s. This is a full-strength reformulation, not a proof of TFS. No transfinite iteration beyond omega is necessary.

## Why a second appeal to the pinned theorem is unavailable

At stage zero let a word v in G*F_n represent an element of finite order k in U. There is an equality

v^k = product_l c_l w_{i_l}^{epsilon_l} c_l^{-1}

in G*F_n. Apply the exponent homomorphism E:G*F_n->Z^n killing G. One obtains

k E(v)=sum_i d_i E(w_i),  d_i in Z.

Thus E(v) is in the Q-row span of A. Adjoining the relation v=1 gives an augmented exponent matrix with a DEPENDENT new row. Theorem 1's full-row-rank hypothesis has been lost. This is not repaired by the fact that v had finite order, or by the fact that G remains torsion free.

The same obstruction persists at every finite radical stage. Inductively all words adjoined earlier have exponent vectors in the original rational row span. If v^k is in their normal closure together with N, then E(v) lies in that span as well. Thus iterative removal of torsion never gives a new independent exponent row to which the pinned theorem directly applies. This calculation does not imply that removal actually kills a coefficient; it identifies precisely why the proposed induction has no available theorem.

One would need to prove coefficient preservation under these dependent torsion consequences. Simply asserting that a quotient of a coefficient-injective group is still coefficient-injective is false, as the explicit singular example in the next checkpoint shows.

## A small paid detection bound

Let V=G_ab tensor_Z Q. Rational abelianization gives

U_ab tensor Q = (V direct-sum Q^n) / span_Q{(c_i,a_i)}.

Here c_i is the total coefficient class of w_i and a_i its exponent row. The map V into this quotient is injective: an element of the span with zero Q^n component has coefficients lambda_i satisfying sum lambda_i a_i=0, so every lambda_i=0 by rank_Q A=m. The rational vector group U_ab tensor Q is torsion free, hence every map to it kills T_omega. Therefore

G intersect T_omega(U) subset ker(G->G_ab tensor Q).

This is a supporting restriction, not the missing theorem: a torsion-free group can have a large rational derived subgroup, including the whole group when it is perfect.
