# Structural229 independent correctness review, round 1

**Proposed verdict for parent adoption: PASS at the entire unchanged frozen statement AND submitted proof.** I find no essential repair, added hypothesis, narrowing, replacement theorem, or unresolved mathematical obligation at that scope. This is only a correctness proposal. No contribution verdict, acceptance, or count is assigned.

The reviewed statement has 2,784 bytes and SHA256 `febac8d7844dbc09a741b31c52bfc05da9d2b9d116ea1bdda42ed19aad0455e9`; the submitted proof has 15,446 bytes and SHA256 `bb9cca632d3a53ae08a60d18448ec2d5a601ec7bfb3a341990065257e73e16ff`. Neither was changed. References below to “proof §k” mean the submitted AUTHOR-PROOF.md, not a repaired proof written by this reviewer. I also read the entire PREFREEZE, MATH-VALIDATION, FINAL, outside author REPORT, and private author READING record. The latter records the author's claimed coverage; my actual coverage and limitations are separately recorded in READING-LIMITS.md.

The conclusion concerns exactly one normalized solution, graph dimension ten, and its specified affine metric. It does not quantify over radial initial data, arbitrary generalized determinant powers, dimensions above ten, or perturbations. All pinned source results and operative proofs are stipulated true. The following checks concern the applications of those premises and the new deductions, not an audit of upstream truth.

## Operative source interfaces and compatible comparisons

At pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, let **S10** denote *Smooth Nonquadratic Affine Maximal Graph in Dimension Ten*, `build/source/main.tex`, and **S3–9** denote *The affine Bernstein theorem in dimensions three through nine*, its main driver and included sections. Fourteen canonical blobs were independently bound to the complete 13,223-entry pinned tree by byte length and Git blob SHA1, as well as to the admitted packet by SHA256 and modes. Authentication alone was not treated as semantic reading.

The exact interfaces used are:

- S10 `prop:reduction`, equations `eq:reduced`, `eq:hessian`, `eq:det`, `eq:w`, `eq:trace`, `eq:radial` (main.tex lines 112–209): the reduction is for (m) radial variables and graph dimension (n=m+1), with (k=m+2), \(\gamma=(m+3)/(m+2)\). Positivity is pointwise, and the Hessian identity is expressly a quadratic-form identity in the original affine coordinates.
- S10 `lem:local`, equations `eq:constants`, `eq:q`, `eq:j`, `eq:fixed-point`, `eq:integral` (210–297): (m=9,k=11,\gamma=12/11), (F(0)=P(0)=1), (D_x^2F(0)=I), (D_x^2P(0)=-(11/9)I), and a smooth fixed point in (s=r^2/2).
- S10 `lem:autonomous`, `eq:regular`, `eq:ratios`, `eq:autonomous` (299–369), `lem:box`, `eq:box` (371–427), and `prop:global` (429–460): the exact three-variable system, its paid box, and global positive continuation. S10 `thm:main` and its proof (53–62, 462–475) supply the smooth entire nonquadratic affine-maximal graph.
- S3–9 main `thm:main` (82–96) is a Euclidean-complete graph theorem only for (3\le n\le9), on a nonempty open convex domain. `sections/rigidity.tex`, `cor:affine-complete` (283–316), imposes connected, open, smooth locally uniformly convex immersion, affine completeness, and classical affine maximality, again only in that dimension range. None of those rigidity conclusions is applied to this ten-dimensional example.
- S3–9 `sections/area.tex`, `eq:affine-area`, `eq:area-covariance`, and `lem:stationarity` (1–69) fix the conormal, determinant, parameter-density, and ambient-affine conventions. I read the complete companion driver, geometry, area, tubes, bounds, rigidity, and included thin-slice figure source, accounting for the driver and nested dependencies; their paid estimates are not new assumptions in the review.

The admitted original r28 mathematical sections were read at their complete retained extent: original lines 15–28, 29–47, 48–53, original bytes [1458,2362), [2362,3571), [3571,4645). Their three section hashes match the retained concatenation. They already give the global metric factorization and affine completeness at the full compatible strength discussed in check 9. No containing history directory, other r28 section, closed target, peer, contribution review, or parent assessment was read.

The actual primary comparisons read include Trudinger–Wang, *Invent. Math.* 140 (2000), §§2–4, 6–7, especially (7.1)–(7.15); Trudinger–Wang, *Invent. Math.* 150 (2002), Theorem A, Corollaries 1–2 and §§2–4, including (2.2), (2.6) and the deferred Lemma 2.4 proof; the affine Plateau preprint `math/0405541v1`, §7; Du `2210.09127v2`, §9; Sun–Xing–Xu `2608.25330v1`, Theorems 1.2–1.3 and §2; and Trudinger–Wang `2610.09385v1`, all §3. The last is newer than the pin and is a comparison, not a stipulated or needed premise. Exact selected text extents and limitations are in the separate reading record.

These comparisons are compatible with the submission: the 2000 power profile is singular at the required origin and cannot replace the selected smooth orbit; the 2002 implication goes from affine to Euclidean completeness, not conversely; generalized determinant powers do not give the classical exponent by substitution; and the newer radial construction supplies a comparison for existence, not the submitted critical-orbit estimates or the ball-volume calculation. No claim about validity of unrelated conclusions of those papers is needed here.

## 1. Normalization, selected solution, origin expansion, and initial strictness

The selected fixed point in S10 is unique on the contraction neighborhood. There is no hidden extra local branch relevant to this normalization. Indeed, any smooth positive normalized radial solution has (y=O(r)), (P'=O(r)), and hence zero integration constants for (y^9) and (y^8P') at zero. It obeys S10 `eq:integral`. With (y/r>0), these identities recover `eq:q`, `eq:j`, and the fixed-point equations on a sufficiently short nonnegative (s)-interval; the same contraction estimate gives uniqueness there. For (r>0), `eq:regular` has a smooth right side on (r,F,P,y>0), so continuation is unique. This explains the single selected source solution; it does not introduce a parameter family.

S10's construction actually gives smooth functions of (s=r^2/2) on both sides of zero. Thus the even expansions, and the derivative bounds on their remainders, are justified by smooth Taylor expansion. In particular,
\[
 F=1+\tfrac12r^2+a r^4+O(r^6),\qquad
 P=1-\tfrac{11}{18}r^2+O(r^4).
\]
Then (y/r=1+4ar^2+O(r^4)) and (y'=1+12ar^2+O(r^4)). The first equation, divided by (r^8), gives
\[
 (y/r)^8y'=1+44ar^2+O(r^4),\qquad
 FP^{-12/11}=1+(\tfrac12+\tfrac23)r^2+O(r^4).
\]
Therefore (a=7/264). Independently expanding the ratios gives
\[
 A=r^2+O(r^4),\quad B=1+\tfrac7{33}r^2+O(r^4),\quad
 C=\tfrac{11}9r^2+O(r^4),\quad D=\tfrac{11}9r^2+O(r^4).
\]
The ratios are smooth functions of (r^2) near zero, since (y/r), (F), (P), and (B) have positive nonzero limits wherever they occur as divisors. Applying (r\,d/dr) yields leading coefficients (2,14/33,22/9) for (A',B',D'), respectively. All are strictly positive for sufficiently small (r>0). The proof is not differentiating a generic big-O bound without regularity.

**Resolution:** the coefficient, normalization, differentiability, and initial strict signs in proof §2 are correct. Local uniqueness is already entailed by the exact source construction and its integral interface, not an added assumption.

## 2. Cooperative comparison and the only possible limiting equilibrium

For the paid polynomial vector field, the off-diagonal derivatives are exactly
\[
 V_{1,B}=A,\quad V_{1,D}=0,\quad V_{2,A}=B,\quad
 V_{2,D}=\tfrac{12}{11}B^2,\quad
 V_{3,A}=11-D,\quad V_{3,B}=D(1-D/11).
\]
They are nonnegative on the entire closed box, including its faces, because (0\le D\le33/7<11). No sign is inferred only on the actual orbit.

Along the globally defined smooth solution, (h=X') satisfies (h'=DV(X)h). On any finite interval ([\tau_0,T]), adding a sufficiently large scalar multiple (MI) makes all entries nonnegative. The Volterra/Picard representation of (e^{M(\tau-\tau_0)}h) is the strictly positive initial vector plus nonnegative terms. In particular its ith coordinate is at least (h_i(\tau_0)>0). Every arbitrarily long finite interval is covered. Choosing \(\tau_0\) in the initial positivity regime handles all later times, while the expansion handles the earlier ones. A uniform positive lower bound as (T\to\infty) is neither asserted nor needed.

The three increasing bounded coordinates have limits. By continuity, a nonzero limiting component of (V(X)) would force a nonzero limiting derivative and contradict convergence. Moreover (A_\infty>0,D_\infty>0), and (B_\infty>1): the last follows already from the strict (7r^2/33) origin correction and subsequent increase. Thus the first two equilibrium equations legitimately give
\[
 B_\infty=A_\infty-1,\qquad
 D_\infty=\frac{11(4A_\infty-9)}{6(A_\infty-1)}.
\]
In particular (A_\infty>2); the denominator cannot vanish. To verify the elimination without numerical test points, multiply the third equation by (36(A-1)). Its numerator is
\[
 66A(2A+3)-528(4A-9)+11(4A-9)(2A+3)
 =55(2A-9)^2.
\]
Consequently (A_\infty=9/2), and the other two values are (7/2,33/7). The root is double. This identity does not by itself give a convergence rate, and the submission does not claim it does. Zero-coordinate boundary equilibria and (A=1) denominator alternatives have already been excluded by the actual monotone trajectory. Strict increase and infinite forward existence force each finite-time coordinate strictly below its limiting value.

**Resolution:** proof §2 establishes the full strict monotonicity and corner convergence. No boundary or denominator case is missing.

## 3. Deficit sign, actual Jacobian, quadratic terms, and Jordan block

Write (z=(a,b,d)=X_*-X). Direct expansion of the actual source polynomial gives, exactly,
\[
 z'=Jz-Q_2(z)+Q_3(z),
\]
where
\[
 J=\begin{pmatrix}-9/2&9/2&0\\7/2&-27/2&147/11\\44/7&132/49&-12\end{pmatrix},
\]
\[
 Q_2(a,b,d)=\left(ab-a^2,\ ab-\tfrac{27}{7}b^2+\tfrac{84}{11}bd,
                  -ad+\tfrac17bd-\tfrac7{22}d^2\right),
\]
\[
 Q_3(a,b,d)=\left(0,\tfrac{12}{11}b^2d,-\tfrac1{11}bd^2\right).
\]
Thus the sign of the quadratic term in deficit dynamics is negative; the cubic has the displayed positive sign relative to the Taylor expansion of (V). The proof's (O(|z|^3)) is valid.

The trace of (J) is (-30). Its three principal second minors are (45,54,126), totaling (225), and its determinant is zero. Hence the characteristic polynomial is \(\lambda(\lambda+15)^2\). For
\[
 v=(1,1,110/147),\qquad \ell=(308,132,147)/550,
\]
row multiplication gives (Jv=0), column multiplication gives (\ell J=0), and (\ell v=(308+132+110)/550=1). Put \(\Pi=v\ell\), (S=I-\Pi). The stable nilpotent part is
\[
 N=(J+15I)S=
 \begin{pmatrix}21/10&9/10&-441/110\\-49/10&-21/10&1029/110\\0&0&0\end{pmatrix}.
\]
It is nonzero and (N^2=0). Therefore the stable eigenvalue has a genuine size-two Jordan block. On (E=\ker\ell), (J=-15I+N), so
\[
 e^{sJ}|_E=e^{-15s}(I+sN)|_E,
 \qquad\|e^{sJ}|_E\|\le C(1+s)e^{-15s}.
\]
This derives the submitted semigroup estimate without diagonalizability. My coefficients and polynomial elimination were derived before inspecting the author's arithmetic helper. The independent read-only polynomial calculation in `independent_math.py` corroborates them; no author helper was executed.

**Resolution:** signs, eigenstructure, projections, and normalization in proof §3 are correct, including the polynomial factor in the stable bound.

## 4. Positive neutral projection and the uniform stable convolution

Since all three components of (z) and all entries of (\ell) are positive, (q=\ell z>0), and
\[
 \|z\|_2\le\|z\|_1\le q/\min_i\ell_i.
\]
It follows that (q\to0), (w=Sz=z-qv\in E), and the nonlinear term (R(z)=-Q_2(z)+Q_3(z)) is (O(q^2)). As (\ell J=0), \(q'=\ell R(z)\), hence \(|q'|\le Cq^2\).

There are two distinct uses of this bound, both valid before any asymptotic rate has been assumed. First,
\[
 (1/q)'=-q'/q^2\le C,
 \quad q(\tau)\ge\frac1{q(T)^{-1}+C(\tau-T)}\ge\frac c{1+\tau}
\]
for sufficiently large positive (T,\tau). Second, (Cq\le\epsilon) eventually, so integrating \(|(\log q)'|\le\epsilon\) backward gives
\[
 q(s)\le e^{\epsilon(\tau-s)}q(\tau),\quad T\le s\le\tau.
\]
The projection commutes with (J); thus variation of constants on (E) is exactly the formula in the submission. Its integral is bounded by
\[
 Cq(\tau)^2\int_0^{\tau-T}(1+h)e^{-(15-2\epsilon)h}\,dh
 \le C_\epsilon q(\tau)^2
\]
for any fixed \(\epsilon<15/2\), including the author's choice \(\epsilon<1\). The initial stable term has size (C(1+\tau-T)e^{-15(\tau-T)}). Dividing by the lower bound for (q(\tau)^2) gives a bounded, eventually vanishing exponential times a cubic polynomial. It too is (O(q^2)).

Hence (w=O(q^2)) uniformly as \(\tau\to\infty\). There is no assumption that the orbit avoids a stable manifold: the componentwise deficit positivity supplies the norm bound and the polynomial lower bound which rule out exponential-only decay. No center-manifold existence or differentiability theorem is invoked.

**Resolution:** the submission supplies the essential analytic argument, not merely a formal neutral-direction expansion. The convolution and initial-term estimates close at the stated scope.

## 5. Neutral coefficient, reciprocal integration, logarithms, and constants

The independent quadratic formula yields
\[
 Q_2(v)=\left(0,\tfrac{20}7,-\tfrac{2530}{3087}\right),\qquad
 \ell Q_2(v)=\tfrac7{15}.
\]
For example, the second entry is (1-27/7+(84/11)(110/147)=20/7), and the third is (-(6/7)(110/147)-(7/22)(110/147)^2). The displayed quadratic map also shows that replacing (z) by (qv+w), with (w=O(q^2)), changes (Q_2) by (O(q^3)); (Q_3(z)=O(q^3)). Therefore
\[
 q'=-\tfrac7{15}q^2+O(q^3).
\]
For (h=1/q), (h'=7/15+O(q)). Since (q\to0), integrating first gives (h/\tau\to7/15), so (q=O(1/\tau)). A second integration gives (h=(7/15)\tau+O(\log\tau)). Inversion is legitimate for large positive \(\tau\), and gives
\[
 q=\frac{15}{7\tau}+O(\log\tau/\tau^2),\quad
 z=\frac{15}{7\tau}v+O(\log\tau/\tau^2).
\]
This is the Euclidean vector error claimed, not just three leading powers without a common bound.

For (F), the renormalized logarithmic derivative is (O(\log\tau/\tau^2)). Its absolute integral from any sufficiently large finite (T) converges, with tail (O((\log\tau)/\tau)). Thus the renormalized logarithm has a finite real limit; exponentiating gives a finite strictly positive (c_F), with relative error (O((\log\tau)/\tau)). Similarly,
\[
 C=BD=\tfrac{33}2-
       \left(\tfrac{33}7+\tfrac72\tfrac{110}{147}\right)q+O(q^2)
   =\tfrac{33}2-\tfrac{22}3q+O(q^2).
\]
Consequently \(\log F\) has the correction (-(15/7)\log\tau), and \(\log P\) has (+(110/7)\log\tau). The same integrable-tail argument gives finite strictly positive (c_P). Restoring \(\tau=\log r\) yields exactly the stated (O(\log\log r/\log r)) relative errors.

From (y=AF/r), (y'=ABF/r^2), the original first radial equation is exactly
\[
 A^9BF^8P^{12/11}=r^{18}.
\]
The radial exponent on the left is (8(9/2)-(12/11)(33/2)=18); the logarithmic exponent is (8(-15/7)+(12/11)(110/7)=0). Taking the limit proves
\[
 (9/2)^9(7/2)c_F^8c_P^{12/11}=1.
\]
The constants are fixed by the one normalized source solution. The algebraic relation does not turn them into a freely variable family.

**Resolution:** the drift, remainder, two integrations, all logarithmic exponents, positive finite constants, and exact constant constraint in proof §§3–4 are established.

## 6. Original affine tensor and the global coordinate pullback

In S10 `eq:hessian` and `eq:det`, the determinant is computed in original affine ((x,t)) coordinates. Its basis change in the reduction proof has determinant one. With (m=9),
\[
 D^2u=\frac FuH+\frac{F^2}{u^3}(dt-(t/F)dF)^2,\qquad
 \det D^2u=F^{11}u^{-12}\det H.
\]
Set (t=F\sinh v), (u=F\cosh v). The pulled-back covector is (dt-(t/F)dF=F\cosh v\,dv). The Hessian tensor therefore pulls back to
\[
 (\cosh v)^{-1}(H+F\,dv^2).
\]
Meanwhile, as a scalar function originally defined by the affine-coordinate determinant,
\[
 F^{11}(F\cosh v)^{-12}(FP^{-12/11})
 =P^{-12/11}(\cosh v)^{-12}.
\]
Its (-1/12) power is (P^{1/11}\cosh v), which cancels every hyperbolic factor and every unintended power of (F). This proves the exact metric identity.

Recomputing a Hessian of (u\circ(x,v)), or recomputing the determinant of the pulled tensor as though it were the original scalar determinant, would be wrong. The submission explicitly avoids both operations. The map ((x,v)\mapsto(x,F(x)\sinh v)) has inverse ((x,t)\mapsto(x,\operatorname{asinh}(t/F(x)))). Smooth positivity of (F) makes both maps global and smooth, including (x=0), and the vertical Jacobian (F\cosh v) never vanishes.

**Resolution:** proof §5 uses the correct tensor pullback and the dimension-ten exponent. There is no coordinate-Hessian substitution.

## 7. The barrier for Q and exclusion of finite-radius degeneracy

The (C) equation is S10 `lem:autonomous`'s displayed intermediate identity:
\[
 C'=C(1+C-8B)+11AB.
\]
Let (E=A-C/11). The origin expansions give (E=(8/9)r^2+O(r^4)>0). At any proposed zero, (C=11A), and direct subtraction gives
\[
 E'=A(8B-12A).
\]
Since (B>0), the paid bound (D=C/B\le33/7) then gives (B\ge7A/3). Thus (E'\ge(20/3)A^2>0). Starting from a sufficiently small fixed radius, a first later zero, if any existed, would have derivative at most zero. This is impossible. Applying this argument to any proposed finite zero proves (E>0) for all (r>0).

Since \(d\log Q/d\tau=E\) and (Q(0)=F(0)P(0)^{1/11}=1), (Q(r)>1) for (r>0), and it strictly increases. All ratios used are legitimate: global (F,P,y,y'>0) is paid; (B>0) and (A>0) follow, and the integrated flux gives (P'<0) at every positive radius. The proof does not postpone a possible finite zero of (P), (y), (F''), or (Q) to its asymptotic argument.

**Resolution:** the barrier sign is correct and uses the actual source box in the required direction. It proves the global lower bound needed later.

## 8. Proper radial coordinate, axis smoothness, and both warp limits

The radial Hessian is (F''dr^2+rF' g_{S^8}). Thus
\[
 \rho'=\sqrt{P^{1/11}F''}=\frac{\sqrt{ABQ}}r>0,
 \quad\phi^2=QA,\quad\psi^2=Q.
\]
At zero the radial coefficient is one. More explicitly, the already justified smooth expansions give
\[
 P^{1/11}F''=1+\tfrac{26}{99}r^2+O(r^4),\quad
 \rho=r+\tfrac{13}{297}r^3+O(r^5),\quad
 Q=1+\tfrac49r^2+O(r^4),\quad QA=r^2+\tfrac5{99}r^4+O(r^6).
\]
Consequently \(\phi^2=\rho^2-\rho^4/27+O(\rho^6)\) and \(\psi^2=1+4\rho^2/9+O(\rho^4)\). These corroborate the regular polar axis. The proof's more direct justification, the globally smooth positive Cartesian tensor, already establishes smooth extension without requiring the reader to infer it from a polar formula.

At infinity, with (K=c_Fc_P^{1/11}>0),
\[
 Q=Kr^3(\log r)^{-5/7}[1+O(\log\log r/\log r)].
\]
Therefore both \(\sqrt Q\) and \(\rho\) diverge. For the latter, \(\rho'\asymp r^{1/2}(\log r)^{-5/14}\), which eventually exceeds a positive constant times (r^{2/5}), as the proof says. In addition
\[
 (\sqrt Q)'=\frac{E\sqrt Q}{2r},\qquad
 \frac{\rho'}{(\sqrt Q)'}=\frac{2\sqrt{AB}}E\longrightarrow\sqrt7,
\]
using (AB\to63/4) and (E\to3). Integrating two-sided derivative inequalities (or the applicable infinity/infinity l'Hopital rule) gives \(\rho/\sqrt Q\to\sqrt7\). Thus
\[
 \psi^2/\rho^2\to1/7,\qquad \phi^2/\rho^2\to(9/2)/7=9/14.
\]
The increasing radial coordinate has range ([0,\infty)), and \(\phi>0\) off the axis, \(\psi\ge1\) everywhere. All limits concern the one fixed solution.

**Resolution:** properness, both constants, and extension across the polar axis in proof §5 hold at exactly the stated scope.

## 9. Completeness and the three distinct metrics

For every piecewise smooth path, the metric speed bounds \(|\dot\rho|\) and \(|\dot v|\): the second uses (Q\ge1). Though \(\rho(|x|)\) is a radial distance function rather than a smooth Cartesian scalar at zero, it is locally Lipschitz; its composition with such paths is absolutely continuous and the derivative bound holds almost everywhere. Hence \(\rho\) and (v) are globally 1-Lipschitz for the intrinsic distance.

A metric-Cauchy sequence has bounded \(\rho,v\). Properness of \(\rho(|x|)\) confines it to a Cartesian compact set. There is a Cartesian convergent subsequence, and smooth positive definiteness gives convergence of that subsequence in (g), by the local upper metric bound on a small convex coordinate neighborhood. The Cauchy property then gives convergence of the full sequence. No minimizer-existence theorem or assumption that minimizing paths remain in the compact set is needed. If one wants explicit local two-sided distance equivalence, use an enlarged compact neighborhood with smallest eigenvalue (m>0): any path leaving it from a smaller compact set pays at least \(\sqrt m\) times their positive Euclidean separation. Sufficiently short near-minimizing paths cannot leave; the lower metric bound then applies. This elaborates, rather than repairs, the submission's local equivalence argument.

The paid original r28 construction has been incorporated at its full compatible strength: (a(r)=FP^{-12/11}) increases from one, and the integrated first equation gives
\[
 r^9\le y^9=9\int_0^r s^8a(s)\,ds\le r^9a(r).
\]
Thus (y/r\ge1), (y'\ge a^{1/9}\ge1), and (H\ge I). The source bound (C\le33/2) gives (P^{1/11}\ge c\max(1,r)^{-3/2}). The base metric has a divergent radial exhaustion \(\sqrt c\int_0^r\max(1,s)^{-3/4}ds\), so it is complete. For the full factorized metric with positive fiber coefficient, short paths between late Cauchy-sequence terms stay in an enlarged bounded base ball; the positive minimum of the fiber coefficient there controls the fiber coordinate. This already proves affine completeness without the new asymptotics or the new global (Q\ge1) bound. The submitted proof correctly acknowledges this supplied construction.

The auxiliary Euclidean-graph assertion is also correct: intrinsic graph distances dominate base Euclidean distances, and the smooth graph lift plus local upper bounds converts a base limit of a graph-Cauchy sequence into intrinsic convergence. This is not used to infer affine completeness. For the original Hessian metric, the axis (x=0) has coefficient (u_{tt}=(1+t^2)^{-3/2}); its length to infinity is \(\int_0^\infty(1+t^2)^{-3/4}dt<\infty\). It escapes every compact set, giving an incomplete Hessian metric and precluding a global positive constant Hessian lower bound. In contrast the affine axis is (dv^2=dt^2/(1+t^2)), of infinite length to either end.

**Resolution:** affine completeness is established without conflating it with Euclidean graph or Hessian completeness, and the older compatible proof is fully accounted for.

## 10. Arbitrary paths, open-ball inclusions, and a uniform outer radius

The axis-then-radial path at fixed final (v) has length \(|v|+\rho\), since \(\psi(0)=1\) and the radial metric coefficient is one. For \(\rho=0\) it is simply the axis path; the choice of angular direction at zero creates no cost or ambiguity. Thus \(d(p_0,p)\le|v|+\rho\).

For the reverse estimate fix (K_0>0) and any finite-length piecewise smooth path from (p_0) to (p). Partition its parameter domain measurably into \(\rho<K_0\) and \(\rho\ge K_0\), and integrate speed to define \(L_{\rm in},L_{\rm out}\). This does not assume finitely many crossings. Monotonicity of \(\psi=\sqrt Q\) and \(\psi\ge1\) imply
\[
 |v|\le\int|\dot v|\le L_{\rm in}+L_{\rm out}/\psi(K_0)
 \le L_{\rm in}+L/\psi(K_0).
\]
The positive part \(f=(\rho-K_0)_+\) is absolutely continuous. Its derivative vanishes almost everywhere where \(\rho\le K_0\); elsewhere \(|\dot f|=|\dot\rho|\) is bounded by speed. Hence
\[
 L_{\rm out}\ge\operatorname{Var}(f)\ge(\rho(p)-K_0)_+.
\]
Points on the threshold may be assigned to the outer set; motion along it obeys the same (v)-bound. Axis passages obey the Lipschitz radial bound from check 9. Combining the two estimates gives
\[
 L(1+1/\psi(K_0))\ge |v|+(\rho-K_0)_+\ge |v|+\rho-K_0.
\]
This holds for every path. Taking its infimum therefore gives the same inequality for (d), with no geodesic or compactness assumption.

With \(D(T)=\{\rho+|v|<T\}\), one obtains exactly
\[
 D(R)\subset B_g(p_0,R)
 \subset D\bigl(R(1+1/\psi(K_0))+K_0\bigr).
\]
The upper inclusion is strict in the defining (D)-inequality because (d<R) and the coefficient multiplying (d) is positive. The lower inclusion uses (d\le\rho+|v|<R). Thus the open-ball convention causes no boundary gap.

Take (K_0=\sqrt R). Since \(\psi(K_0)/K_0\to1/\sqrt7\), for all sufficiently large (R), \(1/\psi(K_0)\le2\sqrt7/\sqrt R\). The outer parameter is therefore at most
\[
 R+(1+2\sqrt7)\sqrt R.
\]
This is a single bound for all (v\in\mathbb R) and all angular directions, including \(|v|\) of order (R), arbitrary repeated excursions, points below the threshold, and points on the axis.

**Resolution:** proof §6 contains the required global estimate. A local conical tensor limit is not being substituted for ball control.

## 11. Density, integration, exact coefficient, and every fixed center

Off the axis, the ten-dimensional volume density is
\[
 d\operatorname{Vol}_g=\phi^8\psi\,d\rho\,d\omega\,dv.
\]
There are eight spherical dimensions, one radial dimension, and one (v) dimension. At zero, \(\phi=\rho+O(\rho^3)\) and \(\psi=1+O(\rho^2)\); hence (W=\phi^8\psi=\rho^8[1+O(\rho^2)]). The Cartesian axis has zero ten-dimensional volume, and there is no nonintegrable singularity hidden by polar coordinates.

At infinity
\[
 W(\rho)\sim\kappa\rho^9,\qquad
 \kappa=(9/14)^4/\sqrt7,
\]
and continuity on compact radial intervals gives a global bound (W\le C(1+\rho^9)). Integrating first in (v\in(-(T-\rho),T-\rho)) gives the exact factor two:
\[
 \operatorname{Vol}_gD(T)=2|S^8|\int_0^T(T-\rho)W(\rho)\,d\rho.
\]
After \(\rho=Ts\), division by (T^{11}) leaves the integrand \((1-s)W(Ts)/T^9\). For (T\ge1), this is bounded by (C(1-s)(1+s^9)), and for each (s>0) it converges to \(\kappa(1-s)s^9\). Dominated convergence applies, including the harmless (s=0) endpoint. Finally
\[
 \int_0^1(1-s)s^9ds=\tfrac1{10}-\tfrac1{11}=\tfrac1{110}.
\]
Thus the coefficient is \(2|S^8|\kappa/110=|S^8|(9/14)^4/(55\sqrt7)\), and the exponent is (11). The latter arises from the additional length-(T) interval of accessible (v), not from changing the manifold's dimension.

Check 10's ball inclusions, with outer radius (R+O(\sqrt R)), transfer this limit to (B_g(p_0,R)), since the outer radius divided by (R) tends to one. For each fixed (p), its finite distance (d_0=d_g(p,p_0)) gives the exact open inclusions
\[
 B_g(p_0,R-d_0)\subset B_g(p,R)\subset B_g(p_0,R+d_0)
 \quad(R>d_0).
\]
Both shifted radii divided by (R) tend to one. This proves the same constant for every fixed center, without a claim uniform in moving centers.

**Resolution:** all constants, the (1/110) integral, factor two, domination, and center transfer in proof §6 are correct.

## 12. Covariance, classical compatibility, and auxiliary scope

The ambient-affine scaling assertion in proof §7 is correct. For any positive conormal second form (H_{ij}=\nu X_{ij}), set \(\omega=|\det(X_1,\ldots,X_n,\xi)|\), \(\nu\xi=1\). The invariant metric is
\[
 g=(\omega^2/\det H)^{1/(n+2)}H.
\]
It is unchanged by positive rescaling of the chosen conormal, transforms as a tensor under a parameter change, has the S3–9 `eq:affine-area` density as its Riemannian volume, and reduces to the stated graph metric when \(\omega=1\). Under an invertible ambient affine transformation (L), the pulled-back second form is unchanged with conormal \(\nu L^{-1}\), while \(\omega\) gains \(|\det L|\). Therefore
\[
 L^*g_{L(M)}=|\det L|^{2/(n+2)}g_M.
\]
For (n=10), write \(\lambda=|\det L|^{1/6}\). Distances scale by \(\sqrt\lambda\), volumes by \(\lambda^5\), and a growth-(R^{11}) coefficient scales by \(\lambda^{5-11/2}=|\det L|^{-1/12}\). Both asserted exponents are exact. “Ambient affine transformation” has its usual nonsingular meaning here, consistent with the cited covariance interface; a singular affine map would not define the hypersurface metric under discussion. This is clarification of the existing geometric convention, not an added hypothesis to the frozen theorem.

The proof invokes only elementary finite-dimensional comparison, Taylor expansion, variation of constants, reciprocal integration, and Riemannian local metric bounds beyond the stipulated source inputs. In particular it uses no unverified center-manifold theorem, global uniform Hessian lower bound for (u), entire Legendre-dual assertion, or generalized-exponent transfer. The source's pointwise convexity convention is respected. The source companion's (3\le n\le9) coercivity and rigidity statements are not extended to (n=10).

The strongest relevant primary alternative to the orbit calculation is the singular power construction of TW2000 §7, with polynomial (8\alpha^2-(n^2-4n+12)\alpha+2(n-1)^2=0); at (n=10) it has the double value \(\alpha=9/2\). It identifies the limiting power corner, but does not determine the nonzero neutral amplitude or the logarithmic tails of the normalized smooth orbit. The newer TW preprint's §3 radial barrier and continuation concern (u=h(r)/t) after the 45-degree ambient rotation. For the source ansatz \(h=F^2/2\); its normalization (h(0)=h''(0)=1) is obtained by \(h_{\rm new}(r)=F(r/\sqrt2)^2\). This is compatible rescaling, not a free asymptotic parameter. No higher-dimensional product remark from that newer paper is used as a premise. Its superlinear-growth hypotheses cannot be applied to this graph, whose central axis has \(u(0,t)=\sqrt{1+t^2}\) and asymptotic linear growth.

For the generalized examples, \(11/12>10/11\), so the classical dimension-ten determinant weight is outside the Sun–Xing–Xu interval. TW2002's affine-completeness theorem has (n\ge2) and the required smooth locally uniformly convex immersion interface; it is consistent with, but is not needed to prove, this example's Euclidean completeness. The affine Plateau Legendre-weight and support reconstruction operations are also not used to assert an entire dual or to preserve the classical PDE under a non-affine coordinate change.

The absence of a proper global tangent-cone assertion is respected everywhere in the frozen statement and proof. The warped limits alone do not justify one, especially with unbounded (v) and a cheap axis. The proof instead supplies the global path estimate it actually needs. The Lean comparator ends in `sorry`; neither it nor a formal build is used as support. Primary extraction limitations and unread classical originals do not hide an essential new premise: the relevant source results are stipulated and the new finite-dimensional and metric arguments have been checked directly above.

## Objections tested, clarifications, and remaining obligations

The substantive failure modes tested were: a different normalization or local branch; unjustified differentiation of an error term; loss of strict positivity at late finite time; another boundary equilibrium; division by zero; wrong sign in deficit dynamics; a diagonalizability assumption; a stable-only orbit; circular use of a polynomial decay rate; nonintegrable profile errors or vanishing constants; a coordinate-Hessian substitution; a reversed Q-barrier sign; an omitted finite-radius singularity; an improper radial coordinate; Cauchy paths escaping the compact set used for metric comparison; repeated threshold crossings or threshold/axis paths; nonuniform ball estimates in large (v); a missing factor two or wrong density power; and an incorrect affine scaling exponent. Each is resolved by the unchanged submitted argument and the operative premises, as detailed above.

The elaborations in this review—local fixed-point uniqueness, the displayed full quadratic and cubic polynomials, an explicit stable nilpotent matrix, compact-neighborhood distance bounds, and the measurable-set interpretation of the path splitting—are clarifications already entailed by the source interfaces or steps written in the submission. They do not replace an argument, change a hypothesis, or narrow any conclusion. In particular the proof itself already contains the positive-projection lower bound, uniform convolution estimate, integrable-tail integration, global Q barrier, and global arbitrary-path comparison; these essential operations have not been supplied for the first time by the reviewer.

No mathematical obligation remains unresolved for this correctness proposal. Artifact authenticity and independent arithmetic are corroborating checks, not mathematical gates. Access limits remain explicit and do not establish exhaustive literature coverage, priority, contribution, or acceptance. Parent adoption alone determines the disposition of this proposed full-scope correctness verdict.
