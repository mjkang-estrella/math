# Author proof: polynomial covers of bounded Lp distance profiles

Status: complete author derivation, not independently reviewed. This is a supporting interface for the unchanged terminal target, not a separate nominee. Classical ingredients are explicitly separated below. All spaces are real. No probability assumption on the underlying measure is needed.

## Statement

Fix p>1, R>=1 and eta>0. There is A=A(p,R,eta)<infinity such that for every Lp(mu), N>=1 centers a_1,...,a_N of norm at most R, and arbitrary U contained in its closed unit ball, there exists U0 subset U with

 |U0| <= (2N+2)^A

such that every u in U has v in U0 satisfying

 max_i | ||u-a_i||p - ||v-a_i||p | <= eta.                 (1)

The empty U uses U0 empty. There is no ambient dimension, measure-space, aspect-ratio, or cardinality dependence in A. U may be the unit sphere or a subset specified by nearest-terminal inequalities. Representatives are actual original-space points. This is an existence assertion with no measurable-selection or computational claim.

## 1. A finite linear-observation cover

Let X be a real Hilbert space or Lr(mu), 1<r<infinity. For any N continuous linear functionals h_i of norm at most one and delta>0, the vectors

 (h_i(x))_{i=1}^N,  ||x||_X<=1,

have an external delta-cover in the maximum norm of size at most (2N+2)^M, where M depends only on r,delta (an absolute Hilbert parameter). External centers need not belong to a prescribed subset of the ball.

Here is a self-contained regularized-dual potential proof. Put q=max(r,2), and take F(x)=||x||_r^r/r when r>=2, F(x)=||x||_r^2/2 when 1<r<2. In Hilbert space take q=2,F=||x||^2/2. There is c_r>0 such that

 F(v)>=F(w)+DF(w)[v-w]+c_r||v-w||^q.                    (2)

For r>=2 the scalar Bregman remainder equals

 (r-1)|h|^r integral_0^1 (1-t)|b/h+t|^(r-2) dt

when h!=0. The integral has a positive infimum over b/h in R: it is positive at every point, continuous, and coercive when r>2; r=2 is immediate. Integrate this scalar inequality. For 1<r<2, write z=w+th, N(t)=integral |z|^r. At regular points the second derivative of ||z||_r^2 is

 2(r-1)N^(2/r-1) integral |z|^(r-2)h^2
 +2(2-r)N^(2/r-2)(integral |z|^(r-2)zh)^2.

Holder gives ||h||_r^2 <= N^((2-r)/r) integral |z|^(r-2)h^2. Thus that second derivative is at least 2(r-1)||h||_r^2. Integration yields (2) with c_r=(r-1)/2. To justify zeros and general measure spaces, first use finite simple functions, integrate over intervals avoiding their finitely many coordinate zeros, and pass across zeros by continuity of the first derivative; |t|^(r-2) is locally integrable. Then approximate w,h by finite simple functions in Lr. An Lr function is supported, up to its zero set, on a countable union of finite-measure sets, so this approximation does not require the original measure to be finite or sigma-finite. F and DF are continuous in norm. The Hilbert case is the usual square identity.

On B={||x||<=1}, define

 Psi(y)=max_{x in B} (y(x)-F(x)),  y in X*.

Reflexivity and weak compactness give a maximizer g(y), unique by (2). Variational optimality at g(y), followed by (2), gives for every z in X*

 Psi(y+z)<=Psi(y)+z(g(y))+C_r||z||^(q'), q'=q/(q-1).     (3)

Indeed, put d=g(y+z)-g(y), use DF(g(y))[d]>=y(d), and maximize ||z||t-c_r t^q over t>=0. This also proves (3) without assuming a separate smoothness theorem for Psi.

Fix an unknown x in B. Start y=0. If some |h_i(x)-h_i(g(y))|>delta, choose the first such i and its sign s so that s h_i(x-g(y))>delta, and replace y by y+alpha s h_i. The nonnegative Fenchel gap

 D_x(y)=Psi(y)-y(x)+F(x)

then decreases by at least alpha delta-C_r alpha^(q'). Choose a positive alpha depending only on r,delta with C_r alpha^(q'-1)<=delta/2. Initially D_x(0)=F(x)<=B_r:=sup_B F. Consequently fewer than 1+2B_r/(alpha delta) updates are possible. At termination every observation error is at most delta.

Every possible terminal y is specified by a word of bounded length in the 2N signed functionals. Therefore the finite collection of g(y) from all words of that length supplies the asserted cover. Its size is at most sum_{j=0}^{M0}(2N)^j <= (2N+2)^(M0+1). The argument works for arbitrary continuous functionals; identification of the entire dual of a general-measure Lr space is unnecessary. Integrals against Lr' functions are such functionals by Holder. This is the classical uniformly convex regularization/mistake-potential mechanism, not a claimed new online-learning result.

## 2. Scalar distance-power factorization for non-even p

Suppose p is not an even integer, and put m=floor(p/2), so m<p/2<m+1. For sigma in {+1,-1}, define c_k(sigma)=binom(p,k)(-sigma)^k and

 H_sigma(r)=|1-sigma r|^p-1-r^p
             -sum_{k=1}^m c_k(sigma)(r^k+r^(p-k)), r>0,
 F_sigma(t)=exp(-pt/2) H_sigma(exp t), t in R.           (4)

An empty sum is zero. The exact symmetry H_sigma(r)=r^p H_sigma(1/r) makes F_sigma even. Near r=0, the Taylor expansion of |1-sigma r|^p through degree m, with its first two t-derivatives, leaves O(r^(m+1)). The additionally subtracted r^p and reciprocal Taylor family contribute O(r^(p-m)); for m=0 the r^p term suffices. Thus F_sigma and its first two derivatives decay exponentially as t->-infinity, at rate at least

 beta=min(m+1,p-m)-p/2>0.

Evenness supplies the other tail. At t=0, F_- is smooth. In F_+, the only nonsmooth term is |1-exp t|^p=|t|^p b(t), with b smooth positive near zero. Its first derivative is continuous because p>1; its second derivative is locally bounded by C(1+|t|^(p-2)), which is integrable. There is no delta contribution in its weak second derivative. Hence

 F_sigma in W^{2,1}(R).                                (5)

This includes odd integer p and the entire range 1<p<2. It excludes even integers only because beta would vanish; those are handled by the exact polynomial below.

Let G_0=(F_++F_-)/2, G_1=(F_+-F_-)/2. Use Fourier convention hat G(omega)=integral G(t) exp(-i omega t) dt. Since G_j and G_j'' are integrable,

 |hat G_j(omega)| <= min(||G_j||_1, ||G_j''||_1/omega^2).

Thus hat G_j is integrable, real, and even. Fourier inversion gives

 G_j(t)=integral cos(omega t) dnu_j(omega),
 dnu_j=hat G_j(omega)domega/(2pi),

where nu_j is a finite signed measure. This inversion can be justified by Gaussian regularization: convolve the continuous L1 function with a Gaussian approximate identity, use its Fourier transform, and pass to the limit by dominated convergence on the integrable hat G_j. No positivity of the Fourier transform is required.

Let H_j=L2(|nu_j|;R^2), and define at a!=0

 phi_j(a)(omega)=sign(a)^j |a|^(p/2)
                 (cos(omega log|a|), sin(omega log|a|)),

with phi_j(0)=0. Let J_j multiply by dnu_j/d|nu_j|. Then ||J_j||<=1 and

 ||phi_j(a)||^2=|nu_j|(R)|a|^p.

For any real a,b, including zero, Fourier inversion and (4) give the exact identity

 |a-b|^p = |a|^p+|b|^p
 +sum_{k=1}^m binom(p,k)(-1)^k sign(a)^k sign(b)^k
       [|a|^(p-k)|b|^k+|a|^k|b|^(p-k)]
 +sum_{j=0}^1 <phi_j(a),J_j phi_j(b)>.                 (6)

All terms involving a zero factor vanish. For nonzero factors, factor |ab|^(p/2) and set t=log(|b|/|a|); G_0(t)+sign(ab)G_1(t)=F_sign(ab)(t). That verifies every sign and homogeneity factor.

Integrating (6) over mu yields an exact Lp distance-power identity. Each Taylor term is a Holder pairing between L_{p/(p-k)} and L_{p/k}. The signed-power features have the same norm as unsigned powers. Both exponents are strictly between one and infinity. The Hilbert feature Phi_j(u)(z,omega)=phi_j(u(z))(omega) satisfies

 ||Phi_j(u)||^2=|nu_j|(R)||u||_p^p.

The integrated remainder is <Phi_j(u),J_j Phi_j(a)>. Products are integrable by Cauchy–Schwarz; the Taylor terms by Holder. One may define the product feature on the sigma-finite support generated by the finitely many Lp functions involved, so no extraneous global product-measure regularity assumption is needed. Alternatively, use the completion of finite simple-function Hilbert features, whose norm identity is the displayed one. It yields the same bilinear identity by Lp approximation. The finite Fourier total variations and all coefficients depend only on p.

## 3. Even integer p

For p=2m, use the exact expansion

 |a-b|^p=(a-b)^p=sum_{k=0}^p binom(p,k)(-1)^k a^(p-k)b^k.

The endpoint terms are |a|^p+|b|^p. Every remaining term is a Holder pairing of signed powers in L_{p/(p-k)} and L_{p/k}, 1<=k<=p-1. Both exponents are in (1,infinity). This includes p=2. No Fourier remainder or limiting argument across an even integer is needed. Constants need not be uniform in p.

## 4. Covering the profiles and retaining actual representatives

For ||u||p<=1 and ||a_i||p<=R, each query power feature in (6) or the even expansion belongs to a fixed-radius ball in its Lr space. Each corresponding terminal test has norm bounded by a constant depending only on p,R. The Hilbert query and test norms obey the same property. The scalar ||u||p^p belongs to [0,1]. The values ||a_i||p^p are fixed across queries.

Normalize each nonzero feature/test pair to unit balls, absorbing its coefficient and norm bounds into a finite weight W_l(p,R). Apply Section1 to each feature with tolerance delta, and cover [0,1] by a delta-grid. There are finitely many factors depending only on p. Hence the product code space has at most (2N+2)^A0 elements. Two queries with the same code have distance-power profiles differing by at most

 2 delta (1+sum_l W_l).

Choose delta so this is at most eta^p. For each nonempty code cell meeting U, choose one actual member v of U. The choice is from a finite family of nonempty sets. These members form U0 with the claimed bound. Since for nonnegative s,t and p>=1,

 |s^(1/p)-t^(1/p)| <= |s-t|^(1/p),

the distance-power bound implies (1). Repeated centers and zero centers cause no problem. If a Hilbert signed measure is zero, omit that factor. A one-element or empty code family is absorbed into the same cardinality bound.

## Dependency and contribution boundary

The result above does not use the stipulated dimension-reduction theorem; it is the proposed bridge to be combined with that theorem through a separate finite enrichment construction. The linear-observation covering mechanism is standard uniformly convex online regularization. Holder duality, Fourier inversion for W^{2,1}, and even-power expansion are classical. The explicit two-end Taylor subtraction and its assembly into an all-p distance-profile cover are authored here; no worldwide novelty claim is made. The complete global assembly is in assembly-proof.md. The later antecedent comparison in paid-profile-bridge.md derives this entire qualitative theorem from classical Lp omega-stability, so this explicit factorization is retained as an alternative author proof within a TECHNICAL/no-nominee packet. No independent proof or contribution gate was run, and no count is requested. No finite diagnostic substitutes for these universal arguments.
