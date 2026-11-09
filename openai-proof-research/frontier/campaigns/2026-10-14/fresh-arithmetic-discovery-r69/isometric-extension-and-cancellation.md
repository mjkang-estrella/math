# Exact isometric extension and stable cancellation

Author construction for the unchanged T101G69 problem. This supplies two supporting operations. The extension cost is proportional to tr(I−B), NOT generally to ||I−B||F². It is useful after original-density deletion, where the trace loss is already paid. It does not yet solve arbitrary-D reduction or the full target.

## 1. An explicit symmetric Gram completion

Let S be a fully symmetric cubic on V with 0<=B(S)<=I. In an orthonormal basis diagonalizing F=I−B(S), write F=diag(epsilon_i), 0<=epsilon_i<=1. For each positive epsilon_i add two new orthonormal coordinates u_i,w_i. Put

  l_i=sqrt(epsilon_i/2),   c_i=sqrt(1−epsilon_i).

Extend S by the fully symmetric coefficients

  T_(e_i,u_i,w_i)=l_i  (all six permutations),
  T_(u_i,u_i,u_i)=T_(w_i,w_i,w_i)=c_i,

and set all other new coefficients to zero. Then B(T)=I exactly.

Here is the full Gram check. The old slice e_i acquires the new-pair off-diagonal matrix L_i=[[0,l_i],[l_i,0]]. Different pairs have disjoint supports, and ||L_i||F²=epsilon_i, so the old-old Gram becomes B(S)+F=I. A new slice u_i has an off-diagonal entry l_i between e_i and w_i and a diagonal entry c_i at u_i. Its squared norm is2l_i²+c_i²=1. The w_i slice is analogous. Distinct new slices have disjoint entry supports, including the two slices of a single pair. Old-new inner products vanish: old slices are supported in the old-old block and at off-diagonal u_j,w_j positions, whereas new slices occupy old-new and diagonal new entries. Thus every cross Gram is zero.

Let O_new=sum_i(u_i^tensor3+w_i^tensor3), and R=S direct_sum O_new. Orthogonality of coefficient supports gives

  ||T−R||HS²
    =sum_i[6l_i²+2(1−c_i)²]
    <=sum_i(3epsilon_i+2epsilon_i²)
    <=5tr F.                                          (1)

Both T and R have multiplication flattening norm at most1. The associator is the difference of two quadratic compositions. Telescoping each composition, putting the total HS norm on T−R and the operator norm on the other cubic, gives

  ||A(T)−A(R)||HS<=4||T−R||HS,
  ||A(T)||HS²<=2||A(S)||HS²+160tr F.                  (2)

No norm proportional to sqrt(dim V) enters. This is a genuine extension preserving every coefficient of S, rather than a claimed global congruence normalizer.

## 2. Stable cancellation of any added unit orthodeco block

For every cubic S on R^m and every k>=0,

  dist(S,O_m)² <=4096 dist(S direct_sum O_k,O_(m+k))².  (3)

No bound on B(S) is needed for this cancellation lemma. Here O_k is any fixed unit orthodeco tensor on the added orthogonal summand.

To prove it, let F0=S direct_sum sum_(a=1)^k e_a^tensor3, choose any O=sum_(j=1)^(m+k) v_j^tensor3, and put E=||F0−O||HS. Write q_aj=<e_a,v_j>. Since F0(e_a,e_a)=e_a,

  e_a_error²:=||e_a−O(e_a,e_a)||²
       =sum_j q_aj²(1−q_aj)²,
  sum_a e_a_error²<=E².                               (4)

The last inequality selects disjoint tensor coordinates (i,a,a) from the total squared norm.

Call row a good if some q_aj>0.9. If there is no such entry, every factor (1−q_aj)²>=0.01, so e_a_error²>=0.01. Hence there are at most100E² bad rows. Good rows select distinct columns because two entries exceeding0.9 cannot occur in the same orthonormal column. If q=q_aj>0.9 is the selected entry, every other row entry has absolute value at most sqrt(1−q²)<0.44. Therefore

  e_a_error² >=0.31(1−q²),
  ||e_a−v_j||²=2(1−q)<=7 e_a_error².                  (5)

Thus the two matched orthonormal frames have total squared discrepancy at most7E².

There is an orthogonal transformation U taking the selected v_j to their matched e_a with ||U−I||F² at most twice this frame discrepancy. One direct proof is constrained orthogonal Procrustes. If A,B are the matched frame matrices, complete them to orthogonal bases. Maximize the trace of U on the complementary blocks by polar decomposition. The result is

  min ||U−I||F²
   =||A−B||F²+2(sum_i(1−s_i))
   <=2||A−B||F²,

where s_i are the singular values of A*B. The equality follows from the common nontrivial principal angles of the frame and complementary subspaces; it also follows by diagonalizing the two projection blocks. The inequality uses sum s_i>=tr(A*B). Zero singular values are allowed and the polar factor can be orthogonally completed.

Applying U to an orthodeco cubic changes it by at most3||U−I||F: telescope the three tensor modes, and use orthonormality in the unchanged modes. Consequently

  ||F0−U^tensor3 O||HS <=(1+sqrt(126))E<sqrt(150)E.     (6)

The transformed orthodeco tensor contains every good e_a as an exact basis factor; all its remaining basis vectors lie in the orthogonal complement. Remove the matched factors and compress to the original R^m. If r is the number of unmatched added axes, r<=100E². The frame-compression lemma of frame-transfer.md bounds the distance of the compressed remaining orthodeco tensor from O_m by4sqrt(r). Together with (6),

  dist(S,O_m)<(sqrt(150)+40)E<64E,

which proves(3). The argument also handles no good rows and k=0.

## 3. What these operations reduce, and what they do not

Suppose an all-error theorem at exact B=I were available, dist(T,O)²<=K||A(T)||HS² in all dimensions. Equations(1)–(3) would then imply

  dist(S,O)² <=constant_K (||A(S)||HS²+tr(I−B(S)))     (7)

for every B(S)<=I. The size of the added summand does not enter the estimate, even if F has high rank and small trace.

After deleting the original D>d0 directions from an exact-isotropic tensor, original-density-deletion.md gives tr(I−B(S))<=2rank Q<=2C/d0. Thus the extension is trace-paid in precisely that setting. However the extended tensor has not been shown to have small operator D. Applying the existing small-D theorem to it would therefore be circular. Equation(7) is a conditional interface, not a proof of the all-error theorem it assumes.

For a general initial B<=2I, tr(I−B) need not be controlled by the strong squared Gram error. For example a slightly shrunken orthodeco tensor has trace deficit linear in the shrinkage and squared Gram error quadratic in it. Accordingly this construction does not by itself close arbitrary-B preprocessing either.

The full target remains unchanged and unresolved. These are author constructions, not an independent verdict or a narrower nomination.
