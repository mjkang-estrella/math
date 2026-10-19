# Conditional short-separable interface; the repair is unpaid

Author support for the unchanged T101G69 target. This is not a full theorem nomination. In particular, the existence assumption below is not deduced from approximate PPT, low rank, or the pinned entropy theorem.

Let T be a fully symmetric real cubic on R^m. Define J(e_r)=X_r, P=JJ*, and beta=||J*J−I||F. Regard P as an operator on real m-by-m matrices, with their Frobenius inner product. Suppose there are L=m+k unit real vectors v_a and positive weights w_a such that

    sum_a w_a v_a v_a*=I,
    Q=sum_a w_a |v_a v_a*><v_a v_a*|,
    ||P−Q||HS² <= E.

Then

    dist(T,O_m)² <= 400(E+k+beta²).                    (1)

No smallness assumption and no dimension factor occur. L is the length of an exhibited real symmetric separable decomposition, not merely rank Q. All norms are unnormalized. The proof uses existing r69 frame compression and a short Choi-to-cubic compatibility argument. It is a sufficient interface; the hard new existence statement is still missing.

## Coisometric compression (credited to r69)

Set a_a=sqrt(w_a)v_a and A=[a_1 ... a_L]. Then AA*=I, 0<w_a<=1, and sum_a(1−w_a)=k. For any real matrix Y,

    <Y,QY>=sum_a w_a(v_a*Yv_a)²
           <=sum_a w_a ||Yv_a||²=||Y||F².

Thus 0<=Q<=I. Put Q4=sum_a a_a^tensor4. The difference Q−Q4 is positive, bounded above by I, and has trace sum_a w_a(1−w_a)<=k. Consequently ||Q−Q4||HS<=sqrt(k).

Choose any m columns A0 and complete its polar factor to an orthogonal U=[u_1 ... u_m]. Since the singular values of A0 are at most one,

    ||A0−U||F²<=m−||A0||F²<=k.

This is exactly the polar-completion operation in r69/frame-transfer.md, including the singular case. Its four-mode version gives

    ||sum_selected a_a^tensor4−sum_i u_i^tensor4||HS
       <=4||A0−U||F<=4sqrt(k).

For each telescoping term the other three factor Grams are positive contractions with diagonal at most one. Their Hadamard product is at most I: apply the Schur product theorem to G<=I successively. Hence the changed factor contributes at most its family Frobenius norm, without a dimension factor. The discarded k columns have Gram H<=I, so

    ||sum_discarded a_a^tensor4||HS²
      =sum_ab H_ab^4 <=sum_ab H_ab² <=k.

Writing P_U=sum_i |u_i u_i*><u_i u_i*|, we obtain

    ||Q−P_U||HS<=6sqrt(k),
    epsilon:=||P−P_U||HS<=sqrt(E)+6sqrt(k).            (2)

This part is a fourth-order adaptation of paid coisometry compression, not a newly solved global rounding step.

## Recovering the symmetric cubic, including its signs

Let S be the support projection of P. Its nonzero eigenvalues are those of J*J. Since |sqrt(lambda)−1|<=|lambda−1| for lambda>=0,

    ||sqrt(P)−S||HS<=beta,  ||P−S||HS<=beta.

Zero eigenvalues of J*J are already included in beta². Therefore

    ||sqrt(P)−P_U||HS<=epsilon+2beta=:delta.

Let K:R^m→Sym_m send e_i to u_i u_i*. Orthogonal Procrustes gives an orthogonal R such that

    ||J−KR||HS²=tr(P)+m−2||K*J||_*
               <=||sqrt(P)−KK*||HS²<=delta².          (3)

Here ||K*J||_*=||K*sqrt(P)||_* because the two products have the same row Gram. Nuclear/operator duality gives ||K*sqrt(P)||_*>=tr(K*sqrt(P)K); expanding the squared norm proves the inequality in (3). This also proves (3) when J is rank deficient.

Use u_i as coordinate axes in all three modes. The tensor A corresponding to KR has A_iir=R_ir and its other entries zero. T is fully symmetric. For each distinct i,r, the orbit of (i,i,r) has A-coefficients (R_ir,0,0). Its squared distance to the subspace of constant triples is (2/3)R_ir². These orbits are disjoint, so

    sum_(i!=r) R_ir² <=(3/2)||T−A||F² <=(3/2)delta².

Set s_i=sign(R_ii), choosing either sign at zero. Orthogonality and |R_ii|<=1 imply

    ||R−diag(s_i)||F²
      =sum_(i!=r)R_ir²+sum_i(1−|R_ii|)²
      <=2sum_(i!=r)R_ir²<=3delta².

The tensor sum_i s_i u_i^tensor3 belongs to O_m, since signs can be absorbed in the basis vectors. Thus dist(T,O_m)<3delta. More precisely (1+sqrt(3))²<8, and Cauchy–Schwarz gives

    dist(T,O_m)²<=8(sqrt(E)+6sqrt(k)+2beta)²
                <=328(E+k+beta²)<=400(E+k+beta²).

## Exact unpaid bridge and comparison with previous work

To derive the full frozen target from (1), it would suffice to construct Q as above with E+k<=K(beta²+C), where C=sum_(r<s)||[X_r,X_s]||F² and K is absolute, for every B<=2I. No such construction has been established here. Assuming that construction as a theorem hypothesis does not settle T101G69.

r69/high-space-completion.md already produces extra approximately fixed modes, with dimension excess paid by C, under exact B=I and small operator density. r69/frame-transfer.md already removes excess orthogonal factors at cost O(k). r69/isometric-extension-and-cancellation.md already gives exact symmetric extensions at trace-defect cost and stable cancellation, without proving the global normalization/deletion step. The short-separable hypothesis here is a different sufficient input to that paid compression mechanism. The Choi-to-cubic argument records how full cubic symmetry restores real unit signs after factor alignment; it does not construct the missing factors.

Exact rank-m PPT separability supplies neither a nearby PPT matrix nor the exact marginal, real symmetric decomposition, or controlled length assumed above. A rank bound and a decomposition-length bound are distinct. No paid exact classification is represented as quantitative stability.

In fact, the desired repair is equivalent up to absolute constants to the frozen target, which is another reason not to count this reformulation as its solution. If an orthodeco O has ||T−O||F²<=K(beta²+C), take Q=P_O and k=0. Since ||J_T||op<=sqrt(2) and ||J_O||op=1,

    ||J_T J_T*−J_O J_O*||HS
       <=(sqrt(2)+1)||J_T−J_O||HS.

Thus E<6K(beta²+C). Conversely (1) turns the proposed repair into the target. The equivalence identifies an exact obligation; it does not reduce its proven difficulty.
