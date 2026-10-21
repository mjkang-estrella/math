# Prefreeze construction notebook — r169

No nominee is frozen. These calculations make the strongest compatible reduction concrete; they are not an author-proof submission or a self-assigned correctness/contribution verdict. All pinned operative results are inputs stipulated true.

## 1. Exact object and normalizations

Fix (0<\kappa<8\), (d=1+\kappa/8\in(1,2)\), (p=2-d\in(0,1)\), (q=2/p\). Let \(\gamma\) be ordinary chordal SLE in \(\mathbb H\) from 0 to infinity, in capacity normalization \(\partial_tg_t=2/(g_t-\sqrt\kappa B_t)\). Let
\[
h(r)=r^d(\log\log(1/r))^{p/2}
\]
near zero, completed as in the explicit source. Hausdorff cost uses diameters. Put \(H(A)=\mathcal H^h(\gamma\cap A)\), with the whole trace, and \(X_R=H(B(0,R))\). The question concerns fixed \(\kappa\); none of the constants below is uniform as \(\kappa\to0\) or 8. Exact scale covariance follows from regular variation: \(H_{R\gamma}(RA)=R^dH_\gamma(A)\), hence \(X_R\stackrel{law}=R^dX_1\). It is not necessary that the completion of \(h\) itself be homogeneous.

Write \(\mu^G\) for the first source's canonical measure with initial mean density
\[
G_0(z)=(2\operatorname{Im}z)^{-p}\sin^{8/\kappa-1}(\arg z).
\]
Its conformal-radius convention is the full radius. Write \(\mu^O\) for Lawler–Rezaei Euclidean Minkowski content, whose initial Green density is \(c_{\rm gr}(\operatorname{Im}z)^{-p}\sin^{8/\kappa-1}(\arg z)\). Consequently
\[
\mu^O=c_{\rm gr}2^p\mu^G.
\]
This equality follows by the continuous increasing process/remaining-potential uniqueness argument, not by equating two differently normalized one-point formulas. Zhan 2610.15066v1 identifies \(H=C_\kappa\mu^O\) as Borel measures. Thus \(H=C_H\mu^G\), \(C_H=C_\kappa c_{\rm gr}2^p\in(0,\infty)\). No numerical value of either constant is determined here. Both measures give the real line zero mass, and double points do not receive repeated length. All comparisons below absorb these fixed constants.

The two pinned exactness theorems, positivity on every positive-time segment, finite expected whole-trace gauge mass in bounded disks, and non-sigma-finiteness at iterated-log exponent 1 are already paid inputs. They are not proposed deductions.

## 2. Euclidean weights really produce the same measure

This is the main applicability check in the reduction. One cannot simply declare the finite-mesh variables to converge, nor apply Fatou to an unidentified random limit.

In a fixed interior disk \(D=B(z_0,r)\) with a fixed relative free collar, let \(\tau_e(z)\) be first live approach to Euclidean distance \(e\), with value infinity on failure. Put
\[
W_e(z)=G_{\tau_e(z)}(z)1_{\{\tau_e(z)<\infty\}},\qquad
N^e_t(dz)=W_e(z)1_{\{\tau_e(z)\le t\}}dA(z).
\]
The explicit source mesh:tail and mesh:normalized-tail give, uniformly in sufficiently fine \(e\), the initial marked domain in the stipulated class, and finite/stopping cutoffs,
\[
\mathbb P\{N^e_\infty(D)>u r^d\}\le C e^{-c u^q}\quad(u\ge u_0). \tag{2.1}
\]
Constants depend on \(\kappa\) and the relative collar only. In particular for all real \(n\ge1\), integration of the survival function yields
\[
\|N^e_\infty(D)\|_n\le C r^d n^{1/q}=C r^d n^{p/2}. \tag{2.2}
\]
Indeed \(n\int_0^\infty u^{n-1}Ce^{-cu^q}du\) is a constant times \(c^{-n/q}\Gamma(1+n/q)\), with the bounded interval \([0,u_0]\) added. Gamma's elementary upper bound gives (2.2).

Here is an explicit adaptation of source mass:construction, rather than an assumed new convergence theorem. Choose deterministic \(e_j\downarrow0\), a countable dense family of compact continuous tests with exhaustion cutoffs, and rational times together with infinity. Each coordinate \(N^{e_j}_t(f)\) is bounded in \(L^2\), by finite covering with disks satisfying (2.1). Diagonal weak extraction in \(L^2\), followed by deterministic convex combinations of tails, gives simultaneous almost sure and \(L^2\) convergence for all listed coordinates. Use exactly one row of convex coefficients across all coordinates. Positivity, increasing time ordering, adaptation and vague convergence extend as in the source.

The conditional weight identity is especially simple. For rational \(t\), and then for bounded tests,
\[
\mathbb E[N^e_\infty(dz)-N^e_t(dz)\mid\mathcal F_t]
 =G_t(z)1_{\{z\in H_t,\ \tau_e(z)>t\}}dA(z). \tag{2.3}
\]
The strict inequality excludes a weight already counted at \(t\). On \(\{z\in H_t\}\), the stopped past has positive distance from \(z\), so the indicator tends to 1. The bound \(\mathbb E G_t(z)\le G_0(z)\) permits dominated convergence in \(L^1(d\mathbb P\,dA)\) on interior compact tests. The same identity at zero gives mean \(G_0dA\). This proves the correct remaining potential for the limiting rational-time process.

There is a short way to check atomlessness without importing unspecified high-order collision constants. For disks of radius \(\delta\) in a fixed compact, (2.2) at \(n=2\) gives limiting squared mass at most \(C\delta^{2d}\). Use smooth cutoffs in slightly enlarged disks; their collars are free in the initial half plane for all sufficiently small \(\delta\), and all sufficiently late meshes satisfy the required relative cutoff. Cover the compact by \(O(\delta^{-2})\) such disks. The expected sum of squared masses is at most \(C\delta^{2d-2}\to0\), since \(d>1\). Fatou excludes atoms. No uniform statement at \(d=1\) has been used.

For finite \(t\), the approximant is supported within \(e\) of \(\gamma[0,t]\). The limiting past is therefore carried by that trace. Equation (2.3), as an equality of conditional measure kernels, says the future measure is carried by open \(H_t\). Hence increments between rational times are carried by the intervening trace segment. Rational left and right limits at any real \(t\) can differ only by an atom at \(\gamma(t)\), so they agree. This constructs the locally continuous increasing process. The source's \(\mathbb E G_t\to0\) gives exhaustion of terminal mass as \(t\to\infty\). All these steps are on one event obtained from a countable determining family.

Its difference from \(\mu^G_t(f)\) is a continuous finite-variation martingale, because both have the same integrable terminal remaining potential. It vanishes. Thus the extracted Euclidean-weight measure is the actual canonical measure. Convexity of \(L^n\) norms and Fatou preserve (2.2); there is no need to claim raw \(N^e\) convergence. Open disks can be reached by continuous cutoff approximation and a slightly larger disk with fixed collar. In particular
\[
\|\mu^G_\infty(D)\|_n\le C r^d n^{p/2}. \tag{2.4}
\]
The argument also works after a fixed ordinary stopping time on the event that this collar is free: condition on that past, use the source's uniform constants and conditional kernel, then use its actual restart equality. It asserts nothing about arbitrary disks whose collar has already been invaded.

## 3. Whole-disk upper bound including the boundary

Cover \(B(0,R)\cap\mathbb H\) by Whitney cells with side comparable to distance from \(\mathbb R\). Cover each cell by a bounded number of smaller disks with, for example, a fourfold free enlargement. At height comparable to \(2^{-j}R\), at most \(C2^j\) disks are needed, each of radius comparable to \(2^{-j}R\). A bounded top layer is included. Thus
\[
\sum_D r_D^d\le C R^d\sum_{j\ge0}2^{-j(d-1)}<\infty. \tag{3.1}
\]
Apply Minkowski's inequality in \(L^n\) to finite subcovers, use (2.4), then monotone convergence. Independence between cells is neither true nor required. The real line is null. We obtain
\[
\|X_R\|_n\le C R^d n^{p/2},\qquad n\ge1. \tag{3.2}
\]
Taking integer \(n=\lfloor(u/(eC))^q\rfloor\) in Markov's inequality proves
\[
\mathbb P\{X_R>uR^d\}\le C e^{-c u^q},\qquad u\ge u_0. \tag{3.3}
\]
This includes the starting-point neighborhood and arbitrarily late returns. There is no last-exit stopping-time assumption. The positive exponent \(d-1\) in (3.1) is the precise boundary summability payment. The Whitney operation already occurs in LR's proof of boundary continuity (Lemma 3.7); the source supplies the sharper local input.

## 4. Matching lower exponent without an illicit mesh-event intersection

Specialize the ordinary-law portion of the explicit source rc:dense proof to time zero, marked point \(i\), angle sine 1 and full conformal radius 2. Its displaced array disk \(\mathcal D\) is a fixed compact subset of \(\mathbb H\), away from the marked point. The ordinary-law event is constructed before the final finite centered change of law. For each fixed integer \(m\ge m_0\) and every sufficiently small deterministic mesh \(v\), it has probability at least \(c e^{-Cm^2}\) and counts normalized sausage area at least \(c m^p\) in \(\mathcal D\). There are \(\asymp m^2\) disjoint counted strips of width \(\asymp1/m\), each contributing \(\asymp m^{-d}\); their costs multiply under successive stopped conditional probabilities. This yields \(m^{2-d}=m^p\) mass at cost \(e^{-Cm^2}\).

Choose a deterministic continuous cutoff \(f\) with compact support in a slightly larger interior disk \(U\), and equal to 1 on \(\mathcal D\). The finite experiment's sausage is bounded by the whole trace sausage tested against \(f\). LR's spatial Minkowski-content construction gives convergence in probability of the latter to \(\mu^O(f)\), first for its determining squares and then by continuous approximation. This uses the whole-trace spatial content result, not a claimed uniform limit for arbitrary random stopping intervals. For fixed \(m\), with \(a_m=cm^p\),
\[
\mathbb P\{\mu^O(f)>a_m/2\}
\ge\limsup_{v\downarrow0}\mathbb P\{Y_v\ge a_m\}
\ge c e^{-Cm^2}. \tag{4.1}
\]
For clarity, the first inequality follows from
\(\mathbb P(Y_v\ge a_m)\le\mathbb P(\mu^O(f)>a_m/2)+\mathbb P(|Y_v-\mu^O(f)|\ge a_m/2)\).
No common success event over all meshes is assumed. The compact cutoff avoids a boundary-of-test ambiguity.

Take deterministic \(R_0\) containing \(U\), use \(H=C_\kappa\mu^O\), and then scale the whole curve from \(R_0\) to any \(R>0\). Choosing \(m\) just large enough that \(c'm^p>u\) proves
\[
\mathbb P\{X_R>uR^d\}\ge c e^{-C u^q}\quad(u\ge u_0). \tag{4.2}
\]
Together (3.3) and (4.2) locate the exact power \(q=2/p\); they do not determine the constant in the exponent.

## 5. Quantitative transforms and what they do not identify

The same survival integration gives, with fixed positive constants,
\[
cR^d n^{p/2}\le\|X_R\|_n\le CR^d n^{p/2}.
\]
For the lower bound integrate over a short interval about \(u\asymp n^{1/q}\). In particular there is an \(a>0\) with \(\mathbb E\exp(a(X_R/R^d)^q)<\infty\), while it is infinite for every sufficiently large \(a\). The exact threshold is not computed.

For \(X=X_1\), \(L(\lambda)=\mathbb E e^{\lambda X}\) is entire as a function of complex \(\lambda\), by uniform domination on compact sets. For real \(\lambda\to\infty\), Young optimization of \(\lambda u-cu^q\), and the matching survival lower bound, give
\[
c\lambda^{q/(q-1)}\le\log L(\lambda)\le C\lambda^{q/(q-1)},\qquad q/(q-1)=2/d.
\]
The lower bound uses \(L(\lambda)\ge e^{\lambda u}\mathbb P(X>u)\) with \(u\asymp\lambda^{1/(q-1)}\). Thus the entire Laplace transform has order \(2/d\). Carleman's sum diverges because \(\|X\|_{2n}^{-1}\gtrsim n^{-p/2}\), so its moments determine its distribution. Neither moment determinacy nor entire-function order supplies an exact large-deviation constant.

## 6. Further compatible regularity composition

This section records the strongest additional composition tested, not a distinct nominee. HY use the gauge \(\psi(r)=r^d(\log^*\log^*(1/r))^{-(d-1)}\), and its Luxemburg variation norm. This \(\psi\) is different from the Hausdorff gauge \(h\). HY Lemma 6.1 bounds the norm of every segment inside a fixed interior rectangle by \(u(1\vee\mu^O(\text{segment})^{1/d})\), with failure at most \(Ce^{-c u^{d/(d-1)}}\). Let \(V_K\) be the supremum of these norms over all segments contained in \(K\). The whole-disk bound controls the mass of all these segments simultaneously. Splitting at mass \(T\) gives
\[
\mathbb P(V_K>v)\le Ce^{-cT^q}+C\exp[-c v^{d/(d-1)}T^{-1/(d-1)}].
\]
With \(T=v^p\), both powers are exactly \(v^2\), since \(p q=2\) and \((d-p)/(d-1)=2\). Thus the compatible inputs give a Gaussian upper bound for \(V_K\).

HY's proof of Proposition 6.3 transfers variation from a boundary rectangle \([R^{-1},R]\times[0,R]\) to an interior rectangle via an independent reverse-SLE map. The averaging step and its dyadic decomposition are unchanged. To avoid an artificial loss of the exponent, keep the logarithmic scaling factor in HY (27):
\[
\psi(a x)\le a^d\log\log(ae^e)\psi(x),\quad a\ge1.
\]
Choose \(a_n=c_d 2^{n/d}/(\log(n+e))^{1/d}\), reduced by a constant if necessary, so \(\psi(a_nx)\le2^n\psi(x)\). A modular value exceeding \(2^n\) at scale \(v\) implies norm exceeding \(v a_n\). The sum resulting from HY (28) is bounded by
\[
C\sum_{n\ge0}2^{n(1+\epsilon)}\exp[-c v^2a_n^2]\le C'e^{-c'v^2}\quad(v\ge v_0).
\]
Here \(a_n^2\) grows exponentially divided by a logarithmic factor; the finite initial terms are harmless. This shows explicitly that the fixed boundary rectangle can be handled by the existing transfer operation, with the improved mass input. Constants depend on \(R,\kappa\); this is not a claim for arbitrary rough domains or for a rectangle containing the starting point. It does not prove a matching lower Gaussian tail.

This calculation was made after reading HY's actual reverse-flow transfer proof, not merely its polynomial-tail statement. It reinforces the decision not to nominate a superficial boundary hypothesis removal: a stronger compatible primary operation is available.

## 7. Decision before any author proof

The closed reductions above consist of source mesh/ribbon estimates, the source's own measure-extraction and uniqueness construction, LR spatial content and boundary decomposition, Zhan's full measure identity, and HY's reverse-flow averaging. The new algebra and the Euclidean-cutoff adaptation are made explicit here to prevent an incompatible-interface objection. They do not expose a distinct nonroutine theorem operation suitable for freezing in this discovery task.

The exact-rate question developed in OBSTRUCTION.md is strictly stronger than these estimates, remains prefreeze, and is not represented as a finding. No theorem has been frozen and then weakened. No prior frozen scope has been renamed or retried.
