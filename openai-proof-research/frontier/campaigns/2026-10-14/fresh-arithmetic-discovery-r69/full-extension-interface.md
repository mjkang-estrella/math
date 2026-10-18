# Full old/new compatibility equations

Author working interface for the unchanged r69 theorem. Unlike the preceding restricted architecture, this permits old-old-new coefficients. The equations below identify the remaining problem; they are not asserted solved.

Let S be the prescribed old cubic, with old indices i,j and new indices alpha,beta. Write

  G_alpha,ij=T_(i,j,alpha),
  L_i,alpha beta=T_(i,alpha,beta),
  C_alpha beta gamma=T_(alpha,beta,gamma).

Every G_alpha and L_i is symmetric; C is fully symmetric. Put (A_i)_(j,alpha)=G_alpha,ij and (R_alpha)_(i,beta)=L_i,alpha beta. The full slice matrices are

  X_i=[[S_i,A_i],[A_i*,L_i]],
  X_alpha=[[G_alpha,R_alpha],[R_alpha*,C_alpha]].

Exact B=I is equivalent to all three Gram equations

  I−B(S)=2 sum_alpha G_alpha²+(<L_i,L_j>)_ij,           (1)

  <S_i,G_alpha>
    +2 sum_(j,beta) G_beta,ij L_j,alpha beta
    +<L_i,C_alpha>=0,                                 (2)

  <G_alpha,G_beta>
    +2 sum_(i,gamma) L_i,alpha gamma L_i,beta gamma
    +<C_alpha,C_beta>=delta_alpha beta.                (3)

The all-old associator equals the associator of S plus the difference of the two appropriate pair contractions of G:

  A_ext,ijkl=A_S,ijkl
       +sum_alpha(G_alpha,ij G_alpha,kl
                   −G_alpha,jk G_alpha,il),           (4)

up to the fixed global convention for ordering the output index. This is precisely the cancellation unavailable when all G_alpha are zero.

If F=I−B(S)>=0, taking the trace in (1) gives

  tr F=2||G||HS²+||L||HS².

For any unit orthodeco cubic O on the new space, the distance to S direct_sum O is exactly

  3||G||HS²+3||L||HS²+||C−O||HS²
       <=3tr F+||C−O||HS².                            (5)

Thus the cross-interface cost is automatically trace-paid once(1) is solved; the real remaining requirements are(2),(3), a trace-paid choice of C, and control of the complete associator density.

For the actual original-density deletion, the original Q-block coefficients provide a solution of(1)–(3) and restore (4) to the original small density on P. But they also restore the original bad Q density. An orthogonal embedding of that same Q block into a larger new space merely rotates the bad density and cannot reduce its operator norm. A successful construction must change the new algebra and its mixed actions, not just relabel or duplicate coordinates.

The exact-nucleus splitting note gives a solved limiting architecture: active nuclear directions act by scaled orthogonal projections on a bad module, and there are at most rank D such directions. Replacing the exact nucleus by the low spectrum of D requires a quantitative repair of these action relations while preserving(1)–(4). That repair, or a different noncascading replacement, remains unpaid.

No all-error exact-isotropy theorem, global normalizer, or trace-versus-squared-Gram inequality is assumed in these equations. The full frozen target remains open.
