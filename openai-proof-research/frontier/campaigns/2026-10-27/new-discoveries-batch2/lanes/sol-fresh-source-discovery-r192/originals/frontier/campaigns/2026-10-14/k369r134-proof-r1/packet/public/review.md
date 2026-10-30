# Independent full correctness review r1 — K369R134

**Verdict: PASS_FULL_K369R134.** The entire unchanged frozen statement passes, relative to the stipulated pinned source and its operative proof operations. There are no required mathematical repairs or unresolved correctness obligations. This verdict includes arbitrary bounded measurable real radial potentials satisfying (M), every stated small positive coupling, every Fourier mode, finite distinct-point strictness, the converse along any small positive coupling sequence, and the examples with their stated endpoint exclusions. It is not a contribution, novelty, acceptance, count, formalization, manuscript, or release verdict.

The frozen scope is SHA256 `690e3b4b2314ac7009a8cf60b24c89961b2e6e01dd21543904156b851e304a88`; the reviewed proof is SHA256 `cab6bb9b3fdb27a126cb6a214f52b83936526449c823ac345fe3010aa2dd6700`. Neither was changed. The argument below is an independent analytic verification of the full chain, including the places where the author's brief estimates require careful endpoint interpretation. No finite diagnostic is used to infer an infinite-mode assertion.

## P1. Normalizations, signed resolvents, and pointwise meanings

Use area measure on the disk and arclength of mass (2\pi) on the circle. Put (A f(p)=\int_D G(p,x)f(x)\,dx). The Green formula with pole (-(2\pi)^{-1}\log|p-x|) gives

\[
G(p,x)=\frac1{2\pi}\log\left|\frac{1-p\bar x}{p-x}\right|,
\qquad A1(p)=\frac{1-|p|^2}{4}.
\]

The last identity follows by applying (-\Delta) to the displayed quadratic, with zero trace. Positivity and symmetry imply the Schur bound (\|A\|_{2\to2}\le1/4), as well as (\|A\|_{\infty\to\infty}=1/4). Explicitly, Cauchy–Schwarz with weight (G(p,x)), followed by integration in (p), gives the Schur bound. These facts imply the Dirichlet inequality (\|\psi\|_2^2\le\frac14\|\nabla\psi\|_2^2): for smooth zero-trace (\psi), test the Green solution (A\psi) to obtain

\[
\|\psi\|_2^2=\int\nabla\psi\cdot\nabla A\psi
\le\|\nabla\psi\|_2\,\langle\psi,A\psi\rangle^{1/2}
\le\tfrac12\|\nabla\psi\|_2\|\psi\|_2,
\]

and pass by density. Thus the positive constant majorant (a\,dx), where (a=eQ), is subcritical with Dirichlet constant (a/4<1) whenever (a<4). The signed form is coercive under the same upper bound because (e v\le a) almost everywhere. There is no sign-dependent spectral assumption.

The boundary normalizations also follow directly. The single inward radial limit of (G(rs,x)/(1-r)) is

\[
P_s(x)=\frac{1-|x|^2}{2\pi|x-s|^2}.
\]

For distinct (s,t),

\[
G(rs,rt)=\frac1{4\pi}\log\left(1+\frac{(1-r^2)^2}{r^2|s-t|^2}\right)
\]

has double radial limit (N_0(s,t)=1/(\pi|s-t|^2)). Moreover (P_s(0)=1/(2\pi)), so (D_0(s,t)=|s-t|^2/(4\pi)). These constants agree with the frozen statement, without a probability-normalized circle measure.

Here is a pointwise signed construction that never applies an (L^2) resolvent to a singular Poisson section. Uniformly in (s,p), (P_s\in L^{3/2}(D)) and (G(p,\cdot)\in L^3(D)), with bounded norms. Indeed (P_s(x)\le C/|x-s|) and (G(p,x)\le C\log(2/|p-x|)); both claims follow by integrating the corresponding radial singularities in two dimensions. Hölder gives (\sup_s\|AP_s\|_\infty\le C). If (T=eAv), then

\[
\|T\|_{\infty\to\infty}\le a/4,
\qquad |T^jP_s(p)|\le C a(a/4)^{j-1}\quad(j\ge1).
\tag{R1}
\]

Every absolute chain is bounded by the same chain with (v=Q). Consequently the series for (K_e(p,s)) converges absolutely at every stated (p\in D,s\in S^1), with a uniformly bounded correction. For distinct (s,t), the first term (\int P_s |v|P_t) is finite: in a small neighborhood of one boundary pole the other Poisson kernel is bounded, and (1/|x-s|) is locally integrable. The remaining boundary-chain terms are bounded by (R1) and (\int_D P_s\,dx=1/2), hence are absolutely summable. Chain reversal gives symmetry. This proves the pointwise and signed meanings, rather than just almost-everywhere Fourier identities.

For completeness, their PDE interpretation uses bounded boundary data before any singular sections. For Lipschitz boundary (h), its harmonic extension (Ah) (here (Ah) denotes the boundary Poisson extension) is bounded and in (H^1). The (L^\infty) Neumann series (W=(I-eAv)^{-1}Ah) is the unique weak solution of ((-\Delta-e v)W=0) with trace (h). Its correction is a zero-trace Green potential of the bounded source (evW); coercivity proves uniqueness. Absolute chain bounds allow the boundary integration to be exchanged with this series and give (W(p)=\int K_e(p,s)h(s)\,ds). Testing the weak equations yields the Dirichlet-to-Neumann bilinear form

\[
\int_D\nabla Ah\cdot\nabla Ak-e\int_D Ah\,v(I-eAv)^{-1}Ak.
\]

Its correction is (\iint R_e(s,t)h(s)k(t)\,ds\,dt), by the same absolute bounds. The harmonic term has off-diagonal negative kernel (-N_0), as can also be verified on each Fourier exponential by its energy (2\pi|n|). Thus (N_e=N_0+R_e) has the asserted boundary interaction interpretation. This argument requires no termwise normal differentiation of an undominated singular series. The interior Green resolvent, if desired for this identification, has integrable logarithmic sections and the usual (L^2) contraction construction; it imposes no reciprocal-inertia assertion.

Radial symmetry makes (K_e(0,s)=k_e) independent of (s), at every (s). Integrating over (s) gives (2\pi k_e=W_1(0)). The boundary-one solution satisfies

\[
\|W_1-1\|_\infty\le \frac{a}{4-a}.
\]

In particular (k_e>0) for (a\le1). The off-diagonal positivity of (N_e) and continuous diagonal extension of its reciprocal are proved below from signed estimates, not borrowed from the nonnegative theorem.

The actual source Section04, especially `lem:kernel-estimates`, explicitly smooths (P_s) once before using (L^2(q)). Its theorem Section05 `thm:negative-kernel` requires a nonnegative bounded density and subcriticality, and allows every interior normalization point. Its positive finite-node update uses a nonnegative update coefficient. That theorem is paid under the stipulation; it does not apply directly to the signed potentials reviewed here. None of the signed CND conclusions above or below is inferred by reversing the sign of such an update.

## P2. Radial Green kernels, path measures, and endpoint interchanges

For (t\ge0), let (L_t=-\partial_r^2-r^{-1}\partial_r+t^2/r^2). At (t>0), its homogeneous solutions are (r^t,r^{-t}). Imposing regularity at zero, zero value at one, and the jump (-[r\partial_r g_t]_{s-}^{s+}=1) gives

\[
g_t(r,s)=\frac{(\min(r,s)/\max(r,s))^t-(rs)^t}{2t}
=(rs)^t\int_{\max(r,s)}^1u^{-2t-1}\,du.
\tag{R2}
\]

The (t=0) limit is (-\log\max(r,s)) and has the same jump. These are inverses with measure (s\,ds), which is essential to the constants in the path integrals. The integral expression gives (0\le g_t\le g_0). The associated operator (A_t) has (\|A_t\|_{\infty\to\infty}\le1/4), since (A_0 1=(1-r^2)/4).

The endpoint factors of a (j)-vertex radial chain are (r_1^t,r_j^t). Inserting the (j-1) integrals in (R2), each internal radius appears twice in the exponent. The total (t)-factor is therefore

\[
\left(\frac{r_1\cdots r_j}{u_1\cdots u_{j-1}}\right)^{2t}=x^t,
\quad \max(r_i,r_{i+1})<u_i<1.
\tag{R3}
\]

The remaining measure is (\prod_i v(r_i)r_i\,dr_i\prod_i du_i/u_i). On this domain (u_i\ge r_i) for (i<j), so (0<x\le r_j^2<1). Pushing this measure forward gives (\nu_j), and replacing every (v) by (Q) gives a dominating positive measure (\nu_j^Q). For (j=1), take (x=r^2) and measure (v(r)r\,dr). In all cases (c_j(t)=\int x^t\,d\nu_j(x)).

There is a direct preliminary proof of finite total mass, so this construction does not assume its later logarithmic derivatives. At (t=0),

\[
\nu_j^Q([0,1])=Q^j\int_0^1 1\,A_0^{j-1}1\,r\,dr
\le\frac{Q^j}{2\,4^{j-1}}.
\tag{R4}
\]

Tonelli applies to the positive integrands; total-variation domination then applies to all signed integrals. The pushforwards have no atom at either endpoint, since (R3) is strictly between zero and one on the domain. The argument does not need this stronger endpoint statement in place of subsequent estimates.

To check the angular kernel pointwise, write (\mathcal P_x(\theta)=(1-x^2)/(1-2x\cos\theta+x^2)). For (x<1), its uniformly convergent geometric Fourier series is (\sum_{n\in\mathbb Z}x^{|n|}e^{in\theta}). Its mass is (2\pi). Ordinary convolution thus satisfies

\[
\frac1{2\pi}\int_0^{2\pi}\mathcal P_x(\alpha-\beta)\mathcal P_y(\beta-\gamma)\,d\beta
=\mathcal P_{xy}(\alpha-\gamma).
\]

The logarithmic Green expansion, or integration of the geometric series with radii separated first, gives

\[
G(re^{i\alpha},se^{i\beta})
=\frac1{2\pi}\int_{\max(r,s)}^1\mathcal P_{rs/u^2}(\alpha-\beta)\,\frac{du}{u}.
\tag{R5}
\]

At coincident interior points both sides have the same infinite logarithmic value; the endpoint with parameter one causes no additional positive-measure set. Integrating Fourier coefficients first gives (g_{|n|}/(2\pi)), consistent with (R2). Boundary Poisson factors are (\mathcal P_r/(2\pi)). A chain with (j) integration vertices has (j+1) such angular normalization factors and (j) angular integrations. Repeated convolution leaves exactly (\mathcal P_x/(2\pi)), with (x) in (R3), not its square root. Hence, pointwise off zero,

\[
R_e(\theta)=\frac1{2\pi}\int\mathcal P_x(\theta)\,d\mu_e(x),
\quad \mu_e=\sum_{j\ge1}e^j\nu_j,
\quad |\mu_e|\le\mu_e^+:=\sum_{j\ge1}e^j\nu_j^Q.
\tag{R6}
\]

For (a<4), (R4) already ensures absolute convergence in total variation. Tonelli proves the positive-chain identity before any signed exchanges. For each fixed nonzero angle, 
\(\sup_{0\le x<1}|\mathcal P_x(\theta)|<\infty\); the same holds on compact angular sets away from zero and for any fixed number of derivatives. Thus total-variation convergence also proves equality of the actual pointwise signed series with (R6), local continuity, and the permitted later differentiations. Since (\int\mathcal P_x=2\pi), (R6) belongs to (L^1(S^1)); Fubini gives

\[
\widehat R_e(n)=\frac1{2\pi}\sum_{j\ge1}e^j c_j(|n|).
\tag{R7}
\]

This proves the angular representation with the correct path exponent, all normalization factors, and signed domination.

## P3. Uniform real-parameter Riccati, coefficient, and difference bounds

The following proof does not use an integer-mode Bessel asymptotic. The series

\[
F_t(z)=\sum_{l\ge0}\frac{(-z)^l}{4^l l!(t+1)\cdots(t+l)}
\]

converges with all fixed (z)-derivatives locally uniformly, uniformly for (t\ge0) on bounded (z)-sets; bound its denominator below by (4^l(l!)^2). Substitution shows that (y_t(r;b)=r^tF_t(br^2)) solves (L_t y=b y), with the regular solution at zero also for (t=0). In a common neighborhood of (b=0), (F_t(b)\ne0), since the same majorant bounds (F_t(b)-1) by a quantity tending uniformly to zero.

Put (u=y_t/y_t(1)), (\phi=r^t), and (h_t(b)=t-y_t'(1)/y_t(1)). The radial Wronskian identity is

\[
\bigl[r(\phi' y_t-\phi y_t')\bigr]'=b r\phi y_t.
\]

The term at zero vanishes: it is (O(r^{2t+2})), including (t=0). Integrating gives (h_t=b\int_0^1r^t u(r)r\,dr). The normalized solution satisfies (u=\phi+bA_tu). Its uniformly convergent Neumann expansion for (|b|<4) therefore gives

\[
h_t(b)=\sum_{j\ge1}b^j c_j^1(t).
\tag{R8}
\]

The ODE-to-integral identity can also be checked directly on (r^{t+2l}):

\[
A_t(r^{t+2l})=\frac{r^t-r^{t+2l+2}}{4(l+1)(t+l+1)}.
\]

It verifies the regular boundary conditions without an unstated singular-endpoint uniqueness theorem.

Termwise series algebra yields (F_t'=-F_{t+1}/[4(t+1)]) and (F_t=F_{t+1}-zF_{t+2}/[4(t+1)(t+2)]). Since (h_t=-2bF_t'(b)/F_t(b)), these two identities give, in a common neighborhood and as a formal identity,

\[
h_t(b)=\frac{b}{2(t+1)-h_{t+1}(b)}.
\tag{R9}
\]

Here is an exact coefficient recursion, rather than an assumed continued-fraction convergence. Let (C_j(t)=[b^j]h_t(b)), (D_t=2(t+1)). Then (C_1=D_t^{-1}), and for (j\ge2),

\[
C_j(t)=\sum_{m=1}^{j-1}D_t^{-m-1}
\sum_{j_1+\cdots+j_m=j-1\atop j_i\ge1}
\prod_{i=1}^m C_{j_i}(t+1).
\tag{R10}
\]

All degrees on the right are smaller. Equivalently, (C_j) is indexed by ordered rooted trees with (j) vertices. A vertex at depth (d), with (m) children, contributes ([2(t+d+1)]^{-m-1}). Every tree contributes positively with multiplicity one. Summing the exponents (m+1) over all vertices gives ((j-1)+j=2j-1). The number (T_j) of these trees has generating series (T(z)=z\sum_{m\ge0}T(z)^m=z/(1-T(z))). Solving the formal quadratic, or its coefficient recurrence, gives (T_j=\frac1j\binom{2j-2}{j-1}=\mathrm{Cat}_{j-1}). Thus the positive-product count and denominator length are exact for every (j).

For a product of (p=2j-1) factors with shifts (l_i\ge1), differentiating (k) times gives

\[
(-1)^k\partial_t^k\left(2^{-p}\prod_{i=1}^p(t+l_i)^{-1}\right)
=2^{-p}k!\sum_{\alpha_1+\cdots+\alpha_p=k\atop\alpha_i\ge0}
\prod_i(t+l_i)^{-1-\alpha_i}.
\]

The number of weak compositions is (\binom{p+k-1}{k}). Consequently (k!\binom{p+k-1}{k}=(p)_k). Combining with (R8)–(R10), and multiplying by (Q^j), proves exactly

\[
0\le(-1)^k(c_j^Q)^{(k)}(t)
\le \frac{\mathrm{Cat}_{j-1}Q^j(2j-1)_k}{2^{2j-1}(t+1)^{2j-1+k}}
\quad(t\ge0,\ j\ge1,\ k\ge0).
\tag{R11}
\]

For (t>0), moment differentiation is justified without presupposing (R11): (x^{t/2}|\log x|^k) is bounded on ((0,1]), so the finite mass (R4) dominates difference quotients in a neighborhood of (t). The logarithmic moment therefore equals ((-1)^k(c_j^Q)^{(k)}(t)). Sending (t\downarrow0), monotone convergence on the positive measure and the continuous rational expression in (R10) give the same finite value at zero. This also proves the one-sided derivative identities at zero by dominated difference quotients, using the now integrable logarithmic moments. There is no use of an unjustified endpoint derivative or of smoothness of (v).

Let (\Delta c(t)=c(t+1)-c(t)). For every integer (k\ge0), finite mass and the finite binomial expansion give

\[
\Delta^k c_j(t)=\int x^t(x-1)^k\,d\nu_j(x),
\quad |\Delta^k c_j(t)|\le\int x^t(1-x)^k\,d\nu_j^Q
\le(-1)^k(c_j^Q)^{(k)}(t),
\tag{R12}
\]

where (1-x\le-\log x). Since 
\(\mathrm{Cat}_{j-1}/2^{2j-1}\le1/2\), summing (R11) at (k=0) gives, for (a\le1/2),

\[
\sum_{j\ge1}e^jc_j^Q(t)
\le\frac{a}{2(t+1)}\frac1{1-a/(t+1)^2}
\le\frac{a}{t+1}.
\tag{R13}
\]

For (b_e(t)=\sum_{j\ge2}e^jc_j(t)), (R11)–(R12) yield

\[
|\Delta^k b_e(t)|\le\frac{a^2}{(t+1)^{3+k}}\,
\frac12\sum_{j\ge2}2^{-(j-2)}(2j-1)_k
=C_k\frac{a^2}{(t+1)^{3+k}}.
\tag{R14}
\]

Each (C_k) is finite, since its summand is a fixed polynomial in (j) times a geometric sequence. In particular the claim holds through (k=6), uniformly on the full real half-line. The same bounds prove uniform absolute convergence there of the coefficient and difference series; positive logarithmic derivative series of any fixed order are similarly dominated. This proves (3.4)–(3.7) at every stated order and for arbitrary measurable signed (v).

## P4. Endpoint estimates and the all-mode (H^6) remainder

By (R13), the (t)-th moment of (\mu_e^+) is at most (a/(t+1)). For (0<h\le1/2), let (N=\lfloor1/h\rfloor). On ([1-h,1]), (x^N\ge(1-h)^{1/h}\ge1/4), and (N+1>1/h). Hence

\[
\mu_e^+([1-h,1])\le4\int x^N\,d\mu_e^+(x)\le4a h.
\tag{R15}
\]

For (h\ge1/2), total mass at most (a) gives the same form with another absolute constant. In particular there is no atom at one. This proves (4.1) without interpreting a moment asymptotic as a measure-density bound.

Let (d=\operatorname{dist}(\theta,2\pi\mathbb Z)). For (x\le1/2), geometric series bound every fixed angular derivative of (\mathcal P_x) uniformly. For (x\ge1/2),

\[
|1-xe^{i\theta}|\ge c((1-x)+d),\qquad
\mathcal P_x=2\operatorname{Re}(1-xe^{i\theta})^{-1}-1.
\]

Each derivative of the latter inverse is a finite sum with denominator powers at most (l+1) and bounded numerators. This proves

\[
|\partial_\theta^l\mathcal P_x(\theta)|
\le C_l[1+((1-x)+d)^{-l-1}].
\tag{R16}
\]

For (0<d\le1), the shell (1-x\le d) contributes at most (C_l a d^{-l}), using (R15). The shell (2^k d<1-x\le2^{k+1}d) contributes at most (C_l a(2^k d)^{-l}), until its radius reaches one. For (l=0) there are (O(1+|\log d|)) shells; for (l\ge1) the sum is geometric. Thus

\[
|R_e|\le Ca L,\quad |R_e^{(l)}|\le C_l a d^{-l}\ (1\le l\le6),
\qquad L=1+|\log d|.
\tag{R17}
\]

The derivatives are justified locally by (R6) and a uniform bound away from zero, before the dyadic estimates are applied. For (d\ge1), all these quantities are (O_l(a)).

Put (w=2-2\cos\theta), (S=\pi wR_e), and (S(0)=0). Since 
\(|w^{(j)}|\le C_j d^{2-j}\) near zero for every (0\le j\le6) (a deliberately weaker bound for (j>2)), Leibniz gives

\[
|S^{(l)}|\le C_l a d^{2-l}L\quad(0\le l\le6),
\qquad \|S\|_\infty\le C_Sa.
\tag{R18}
\]

Choose an absolute (a_0\le1/2) with (C_Sa_0\le1/2). Then, off zero,

\[
N_e=\frac{1+S}{\pi w}>0,\quad
f_e=\frac{\pi w}{1+S},\quad f_e(0)=0.
\tag{R19}
\]

This proves continuity on the circle and the positive off-diagonal kernel, including the approach to the diagonal. Symmetry makes (f_e) real even.

For the first component of the reciprocal remainder, set (B=R_e-eR_1). Its Fourier coefficients are (b_e(|n|)/(2\pi)). The Fourier polynomial of (w^2) is (6-4z-4z^{-1}+z^2+z^{-2}). Thus, for (n\ge2),

\[
\widehat{w^2B}(n)=\frac{\Delta^4 b_e(n-2)}{2\pi}.
\tag{R20}
\]

This includes (n=2), whose five arguments are (0,1,2,3,4), not negative parameters. For (n\le-2), evenness gives the identical formula with (|n|). The remaining coefficients are exactly

\[
\widehat{w^2B}(0)=\frac{6b_e(0)-8b_e(1)+2b_e(2)}{2\pi},
\quad
\widehat{w^2B}(\pm1)=\frac{-4b_e(0)+7b_e(1)-4b_e(2)+b_e(3)}{2\pi}.
\]

They are (O(a^2)) by (R14). On both tails, (R14) with (k=4) gives (O(a^2(|n|-1)^{-7})). Therefore

\[
\sum_{n\in\mathbb Z}(1+n^2)^6|\widehat{w^2B}(n)|^2\le Ca^4,
\tag{R21}
\]

since the tail is bounded by (Ca^4\sum_{n\ge2}n^{-2}). This addresses positive, negative, crossing-zero, and low modes individually.

The second, genuinely nonlinear component is (U=w S^2/(1+S)). The following exact derivative scheme includes all terms at each order (0\le l\le6). Let (F=(1+S)^{-1}). Leibniz writes (U^{(l)}) as the sum over (j+p+q+s=l) of

\[
\frac{l!}{j!p!q!s!}\,w^{(j)}S^{(p)}S^{(q)}F^{(s)}.
\tag{R22}
\]

For (s\ge1), expand (F(\theta+h)) as a geometric series in (S(\theta+h)-S(\theta)) and compare coefficients. This gives

\[
F^{(s)}=\sum_{\alpha_1+2\alpha_2+\cdots+s\alpha_s=s}
\frac{(-1)^M M!s!}{\prod_i\alpha_i!(i!)^{\alpha_i}}
\frac{\prod_i(S^{(i)})^{\alpha_i}}{(1+S)^{M+1}},
\quad M=\sum_i\alpha_i.
\tag{R23}
\]

For (s=0), use (M=0), the empty product, and (F) itself. Each derivative term in (R22)–(R23) has (m=M+2\ge2) factors from (S), (m\le l+2), and total derivative order (l), including that on (w). Its denominator is bounded because (|S|\le1/2). By (R18), its absolute value is at most

\[
C_l a^m d^{2+2m-l}L^m
\le C_l a^2 d^{6-l}L^{l+2}
\quad(0<d\le1,\ a\le1).
\tag{R24}
\]

The last inequality uses (m\ge2), (m\le l+2), and (L\ge1). It does not divide by (v), differentiate (v), or assume any radial regularity. There are only finitely many terms for each (l\le6); their combinatorial coefficients are absolute constants.

For (l\le5), (d^{6-l}L^{l+2}\to0) on both sides of the circle point zero. For (l=6), the bound is (C a^2L^8\in L^2). More explicitly, its squared local integral, and those of every lower derivative, are bounded by constants times

\[
\int_0^\infty e^{-(13-2l)u}(1+u)^{2l+4}\,du<\infty,
\qquad 0\le l\le6.
\]

Define the classical derivatives through order five to be zero at zero. They have matching traces. Integrating by parts on ((-\pi,-\eta)\cup(\eta,\pi)), the boundary terms at zero involve only these derivatives through order five and tend to zero; the integrals converge by the (L^1) bounds implied by (R24). At (-\pi,\pi) periodic traces match, since there is no singularity there. Repeating this argument one derivative at a time proves that the displayed functions are the distributional derivatives through order six. In particular no delta mass or derivative of a delta mass is produced. Their (L^2) bounds give

\[
\|U\|_{H^6}\le C a^2.
\tag{R25}
\]

The reciprocal identity is exact:

\[
f_e=\pi w-e\pi^2w^2R_1+E_e,
\quad E_e=-\pi^2w^2B+\pi U.
\]

Combining (R21) and (R25) proves

\[
\|E_e\|_{H^6}\le C e^2Q^2,
\qquad |\widehat E_e(n)|\le C_E e^2Q^2(1+|n|)^{-6}.
\tag{R26}
\]

Here (H^6) may be defined by the Fourier norm in (R21) or by square-integrable weak derivatives through six. To specify the standard operation used, Parseval for periodic (L^2) functions says the latter norm has Fourier weights (\sum_{l=0}^6 n^{2l}), comparable with ((1+n^2)^6). Conversely a Fourier sequence with this weighted square sum defines all weak derivatives by their (L^2) Fourier series, checked against trigonometric polynomials and then smooth tests. This proves the implication used in (R21) without an additional smoothness hypothesis. The pointwise coefficient estimate in (R26) follows by keeping a single term in this weighted square sum and changing an absolute constant. This completes the crucial all-mode estimate.

## P5. Exact Fourier margin, one constant, strictness, and necessity

For (n\ge2), the five indices in the Fourier product (w^2R_1) are nonnegative. Since (\widehat R_1(n)=(2\pi)^{-1}\int_0^1v(r)r^{2|n|+1}\,dr), the polynomial (1-4x+6x^2-4x^3+x^4=(1-x)^4) gives

\[
\widehat{w^2R_1}(n)=\frac1{2\pi}\int_0^1v(r)(1-r^2)^4r^{2n-3}\,dr
=\frac{m_{n-2}}{2\pi}.
\]

Thus, with the exact sign and factor,

\[
\widehat f_e(n)=-\frac\pi2 e m_{n-2}+\widehat E_e(n)\quad(n\ge2).
\tag{R27}
\]

Substitute (x=r^2) and integrate the beta integral by parts four times:

\[
\beta_n=\frac12\int_0^1x^{n-2}(1-x)^4\,dx
=\frac{12}{(n-1)n(n+1)(n+2)(n+3)}.
\tag{R28}
\]

For (n\ge2), ((n-1)n\le(n+1)^2) and ((n+2)(n+3)\le(20/9)(n+1)^2), so (\beta_n\ge(27/5)(n+1)^{-5}\ge(n+1)^{-5}). Under (M), (m_{n-2}\ge\delta\beta_n). If (e\le c\delta/Q^2), then (R26) gives

\[
|\widehat E_e(n)|\le C_E c\,e\delta(1+n)^{-6}
\le C_E c\,e\delta\beta_n.
\]

Choosing (c\le\pi/(4C_E)) leaves at least half the favorable leading coefficient in (R27). This proves exactly the frozen bound 
\(\widehat f_e(n)\le-(\pi/4)e\delta\beta_n\) for every (n\ge2), including (n=2); no large-mode-only restriction is present.

For (n=1), the base coefficient is ((\pi w)\widehat{\ }(1)=-\pi). Equation (R19) gives

\[
\|f_e-\pi w\|_\infty\le C_1 a
\]

with an absolute (C_1) whenever (a\le a_0). Thus the mode-one bound holds if (a\le\pi/(2C_1)). Fix once and for all any positive (c) no larger than

\[
\min\{a_0,\ 1,\ \pi/(4C_E),\ \pi/(2C_1)\}.
\tag{R29}
\]

These constants were derived with fixed derivative orders at most six, so are independent of (v,Q,\delta,n). The condition (0<\delta\le Q) implies (a=eQ\le c\delta/Q\le c), satisfying every earlier threshold. This works also for arbitrarily small or large (Q); the coupling occurs only through (eQ) and (e^2Q^2). No constant is chosen separately for a particular mode or potential.

Absolute Fourier convergence follows directly from (R27): (|m_{n-2}|\le Q\beta_n=O(Qn^{-5})) and (R26) has summable (n^{-6}) tails. The low modes are finite because (f_e) is continuous. The absolutely convergent series represents (f_e) everywhere: its sum is continuous and has the same Fourier coefficients; a continuous function with all coefficients zero is zero, by convolution with the Fejér kernels, which have mass one, are nonnegative, and concentrate at zero. This is the precise Fourier uniqueness operation being used, and includes the diagonal value (f_e(0)=0).

For finite real coefficients (a_i), absolute convergence permits

\[
\sum_{i,j}a_i a_j f_e(\theta_i-\theta_j)
=\sum_{n\in\mathbb Z}\widehat f_e(n)
\left|\sum_i a_i e^{in\theta_i}\right|^2.
\tag{R30}
\]

If their sum is zero, the constant mode drops out. Equations (R27)–(R29) make every other mode strictly negative for (e>0). For distinct (s_i=e^{i\theta_i}), the matrix ((s_i^n)_{0\le n\le m-1,1\le i\le m}) has determinant (\prod_{i<j}(s_j-s_i)\ne0). A nonzero coefficient vector cannot annihilate all these moments. The zeroth already vanishes, so one positive mode from (1\) to (m-1) is nonzero, and (R30) is strictly negative. Repeated points can be combined for the semidefinite assertion. Since (D_e(s,t)=k_e^2f_e(\theta_s-\theta_t)), with (k_e^2>0), all these conclusions transfer to the required normalization. Continuity was proved in (R19).

At (e=0), (D_0=w/(4\pi)). Its nonconstant Fourier coefficients are (-1/(4\pi)) at (n=\pm1) and zero elsewhere, so (R30) proves semidefiniteness. There is no assertion of finite-set strictness in this case.

For the converse, a continuous real even translation-invariant CND kernel has nonpositive nonzero Fourier coefficients. To derive this from finite CND, fix (n\ge1), use a uniform grid of size (L>2n), and coefficients ((2\pi/L)\cos(2\pi nj/L)). Their sum is exactly zero by the geometric sum of roots of unity. Continuity lets their quadratic forms converge as (L\to\infty) to

\[
\int_0^{2\pi}\int_0^{2\pi}
f(\theta-\phi)\cos(n\theta)\cos(n\phi)\,d\theta\,d\phi
=2\pi^2\widehat f(n)\le0.
\]

The last equality uses only Fourier orthogonality and evenness; it does not assume an absolutely convergent Fourier series. For an arbitrary bounded real radial (v), all of P1–P4 and (R27) hold at sufficiently small positive (e) without (M). Along any positive sequence tending to zero for which (D_e) is CND, the positive center normalization therefore gives (\widehat f_e(n)\le0). Fixing (n\ge2), dividing (R27) by (e), and using (|\widehat E_e(n)|/e\le C_E eQ^2(1+n)^{-6}\to0), gives (m_{n-2}\ge0). Every (k\ge0) occurs. The argument needs neither a rate nor an interval of couplings, and makes no assertion of sufficiency on the boundary of the moment cone.

## P6. Signed examples, boundaries, and primary-input compatibility

The ratio for (v(r)=r^2-b), at weighted moment index (k\ge0), is

\[
\frac{B(k+2,5)}{B(k+1,5)}-b=\frac{k+1}{k+6}-b.
\]

It increases with (k), since its successive difference is (5/[(k+6)(k+7)]>0), and its minimum is (1/6-b). For (0<b<1/6), the essential supremum is (Q=1-b), (\delta=1/6-b>0), and (\delta\le Q). The potential changes sign at (r=\sqrt b) with two positive-measure sign regions. Thus it satisfies the full theorem, with exactly the stated constants. For every (b>1/6), (m_0=(1/10)(1/6-b)<0). Equation (R27) at (n=2) and the (O(e^2Q^2)) error make (\widehat f_e(2)>0) for all sufficiently small positive (e), so the converse Fourier test rules out CND. This includes (b\ge1); the value (Q=1-b) is claimed only in the positive example range, not there. At (b=1/6), (m_0=0); nothing above assigns a sign to the next-order coefficient, and no conclusion is included.

The allowed sufficient endpoint (\delta=Q>0) causes no loss: since (v\le Q) almost everywhere, (M) at (k=0) forces (v=Q) almost everywhere, by strict positivity of the weight on ((0,1)). The estimates already include that case. (Q=0) is outside the sufficient statement; in the converse it gives (v=0) almost everywhere and all moments are zero. Signed potentials are equivalence classes for the integrals, so changing a representative on a null set causes no issue.

The actual Agler–McCarthy author version begins with a complex finite-valued strictly positive-definite kernel on each finite set of distinct points. Section1 assumes irreducibility, meaning no entry (k(x,y)) vanishes. Theorem1.2 concerns positive semidefiniteness of the normalized matrices (1-k_{in}k_{nj}/(k_{ij}k_{nn})); Corollary1.12 gives exactly one positive eigenvalue of ((1/k_{ij})) for every finite set under those kernel hypotheses. Its Schur-complement proof uses a finite positive diagonal entry. These are contextual results here. The singular Green function has infinite diagonal and is not identified with such a reproducing kernel. The source establishes its own regularization/update/limit argument under the stipulated pin. The signed proof reviewed here instead uses (R30), so it imports neither a singular-Green RKHS claim nor a hidden complete Pick hypothesis.

Rozenblum's arXiv:1012.3528v1 Sections2.2.2–2.3.1 treats bounded real radial symbols by diagonalizing the quadratic form in the monomial/spherical basis; in the complex ball it gives the moment quotient in equation (2.5). For the weighted disk form relevant to the first variation, the direct calculation is

\[
\int_D v(r)(1-r^2)^4\left|\sum_{k=0}^M a_k z^k\right|^2\,dx
=2\pi\sum_{k=0}^M |a_k|^2\int_0^1v(r)(1-r^2)^4r^{2k+1}\,dr.
\]

This is just the finite angular orthogonality calculation, so no unprovided Toeplitz asymptotic, compact-support requirement, or infinite-series exchange is used. If an infinite analytic expansion in the weighted Bergman space is desired, its polynomial truncations converge in the weighted (L^2) norm by angular Parseval and monotone convergence of the nonnegative norm series; bounded (v) then passes the form by continuity. The frozen theorem itself is proved by (R27), without needing that extension.

No part of this review extends the result to off-center signed normalization, nonradial (v), arbitrary coupling, interior reciprocal inertia, eigenfunctions, or a complete Pick RKHS. No historical eigenmap/fold or projection-body target is reopened. No contribution or priority conclusion is drawn.

The separate prefreeze first-variation identity is also consistent analytically, although it is not needed for (R27). For real atomic coefficients with \(\sum a_i=\sum a_i s_i=0\), every row of the base squared-chordal matrix annihilates this vector. Consequently the differentiated center factors contribute zero to the base quadratic form. Differentiating the absolutely convergent chains at zero leaves

\[
Q'_0=-\frac14\int_D v(z)\left(6B_0^2-8|B_1|^2+2|B_2|^2\right)\,dx,
\qquad B_j=\sum_i a_i s_i^jP_{s_i}(z).
\]

Let \(A(z)=\sum_i a_i/(1-\bar s_i z)\). Its constant and linear Taylor coefficients vanish, so \(H=A/z^2\) is analytic at zero. The elementary rational identity for \(P_s\), together with the two moment cancellations, gives

\[
2\pi B_0=A+\bar A,\quad
2\pi B_1=zA+\bar A/\bar z,\quad
2\pi B_2=z^2A+\bar A/\bar z^2.
\]

These equations extend at zero by their removable limits. In the indicated quadratic combination the coefficients of \(A^2\) and \(\bar A^2\) are \(6-8+2=0\); the coefficient of \(|A|^2\) is

\[
\frac{12-8(r^2+r^{-2})+2(r^4+r^{-4})}{4\pi^2}
=\frac{(1-r^2)^4}{2\pi^2r^4}.
\]

Thus \(Q'_0=-(8\pi^2)^{-1}\int_Dv(1-r^2)^4|H|^2\,dx\), exactly the prefreeze identity. All differentiated finite-configuration terms are dominated by their small-coupling absolute chain majorants from P1. The weighted expression on the right is integrable even near its finitely many boundary poles: \(H=O(|z-s_i|^{-1})\) there, while \((1-r^2)^4=O(|z-s_i|^4)\). No finite first-variation diagnostic supplies the nonlinear step in P4.

## Review disposition and evidence limits

P1–P6 are discharged at the full frozen scope. Required repairs: **none**. In particular, the real-parameter coefficient inequality, the signed high-order difference estimate, the negative and low Fourier modes, and the absence of weak-derivative point masses have been verified analytically above. These are not obligations deferred to a future manuscript or repaired by a restricted example.

The public working notes record intermediate checks. The separate provenance file records actual read extents, authentication, late observation times, exclusions, and omitted bodies. The copied author diagnostic reproduces 177 bounded exact checks; copied artifact controls reproduce 9 expected cases, including 6 negative cases. These supply only algebra and artifact support. The present verdict rests on the analytic derivation, not those checks. The pinned source is stipulated true and was not truth-audited. All other original roots remain read-only; preservation is checked for the actual author root and named inputs over the recorded observation interval, not claimed historically for a whole parent workspace.
