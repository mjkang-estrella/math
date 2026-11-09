# Global preprocessing for the strong algebraic residual

Author supporting lemma for a possible extension beyond small residual. This uses beta²=||B−I||F², NOT the analytic source penalty Omega(B). It does not establish the full global algebraic or entropy estimate.

Let T be any fully symmetric cubic, B=mu mu*, beta=||B−I||F, a=||A(T)||HS. Let P be the spectral projection of B onto [1/2,3/2], and Q=I−P. Work with S=P^tensor3 T as a cubic on PV. Then

rank Q≤4beta²,
||T−S||F²≤18beta²,
0≤B(S)≤(3/2)I_P,
||B(S)−I_P||F≤6beta,
||A(S)||HS≤a+6beta.                                     (1)

Moreover

dist(T,O_V)²≤dist(S,O_P)²+44beta².                       (2)

The zero-dimensional retained space is allowed, with its tensor and distance equal to zero.

## Proof

For a discarded eigenvalue lambda≥0 outside[1/2,3/2], the elementary scalar inequalities

1≤4(lambda−1)², lambda≤6(lambda−1)²,
lambda²≤9(lambda−1)²

hold. Hence rankQ≤4beta², tr(QB)≤6beta² and ||QBQ||F≤3beta.

The three mode projections commute orthogonally. Their union bound, and symmetry of T, give

||T−P^tensor3 T||F²≤3||Q acting in one mode on T||F²
=3tr(QB)≤18beta².

The compressed flattening has B(S)≤PBP≤1.5I_P. Put M=PBP−B(S)≥0. Its trace consists of squared coefficients with output in P and at least one input in Q, and therefore tr M≤2tr(QB). Also ||M||op≤1.5. It follows that

||M||F²≤1.5tr M≤3tr(QB)≤18beta².

Thus ||B(S)−I_P||F≤||P(B−I)P||F+||M||F≤(1+sqrt18)beta<6beta.

For the associator, restricting all external indices to P gives

A(S)(x,y,z)=P A(T)(x,y,z)
 −P mu(Q mu(x,y),z)+P mu(x,Q mu(y,z)), x,y,z∈PV.

Let Z:QV→PV⊗PV have coefficients Z_(i,j),k=T_kij for i,j in P and k in Q. Then Z*Z≤QBQ, because its Gram sum is obtained by retaining only the two-good-input terms of the full flattening Gram matrix. Each of the two error tensors above, after a permutation of its four indices, is ZZ*. Consequently its HS norm equals ||Z*Z||F≤||QBQ||F≤3beta. Here the inequality follows from positive-semidefinite order: if0≤M≤N, tr M²≤tr MN≤tr N². This avoids the wasteful bound ||Z||F², which would introduce beta² in an unsquared associator estimate. Hence a(S)≤a+6beta.

Finally choose any normalized odeco tensor E_Q on QV, with norm²=rankQ. The tensors T−S and E_Q lie orthogonally to the all-P tensor space. Therefore, for any O_P∈O_P,

||T−(O_P+E_Q)||F²
=||S−O_P||F²+||(T−S)−E_Q||F²
≤||S−O_P||F²+2||T−S||F²+2rankQ
≤||S−O_P||F²+44beta².

Taking the minimum proves(2).

## What remains for global correction

It would now suffice to prove a squared-distance bound for all fully symmetric tensors with B≤1.5I, at cost proportional to beta²+a². This is still not proved.

At exact B=I, the Dirichlet matrix D from associativity-correction.md is positive with trD=C. Deleting D-eigenvectors above tau costs at most C/tau directions, and deleting those directions from a symmetric tensor costs at most three times their number in squared norm. On the retained vectors, the one-versus-three flattening of the associator has small operator norm.

However the homotopy errors Q1,Q2 contract TWO indices. Their matrix-product estimate requires control of a two-versus-two flattening, equivalently the relevant reshuffling S−K, not merely the one-versus-three Gram matrix2D. K restricted to the orthogonal complement of the slice span is not controlled by D alone. Neither rank counting nor compression leakage bounds establish the needed contraction.

Even at the abstract linear-operator level, equal HS norms and contractivity do not supply this inference: let P=diag(I_m,0) and K=diag(sqrt(1−1/m)I_m,1). Then both squared HS norms equal m, P(I−K)P has operator norm tending to zero, but ||K−P||op=1. This example is NOT asserted to arise from a fully symmetric cubic or a CP channel. It only shows why the additional tensor structure must actually be used before making the proposed inference.

The proved small-residual GR notes remain unchanged. This preprocessing is a classical projection/Gram calculation with exact constants, not a separate campaign nominee or a weakening of the entropy target.
