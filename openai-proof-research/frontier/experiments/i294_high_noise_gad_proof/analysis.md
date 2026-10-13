# I294 — independent reconstruction of the I289 proof

2026-10-13. **PASS: unchanged original target and stated same-proof extension.** No minimal repair is needed. Contribution and priority are outside this assignment. The user's later metadata update makes the current total 13/20; this review changes no count. Pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true by stipulation. Their hypotheses and specialization are checked below, rather than their upstream truth.

## 1. Frozen target and independence

The complete target analysis has SHA256 `063466c7963eb9696af1d6fe4e07a3bbb328842a55b4ecfa09b6759004be9e02`; the complete report has SHA256 `4e68aa6bcfd55732a9dc2f08240e56928beacae44fd6deb7a4a744a6f4eb9fbe`. I read both fully, together with the authored reading log, literature, authentication, and authorized parent supplement. Their declarations of correctness are objects of this review, not premises. In particular the author's covariance calculation and the parent's bridge are shared input, not earlier independent validation.

For a fixed finite n >= 1 and normalized pure psi on n qubits, put

\[
A_s=A_{1-s^2,1/2},\quad m_s=h((1+s)/2),\quad
D_n(\psi)=S(A_s^{\otimes n}(P_\psi))-nm_s.
\]

Entropy is in natural logarithms. The target is the infimum of the **squared unhalved** trace norm over equatorial pure products, bounded by

\[
\frac{240+32/(1-s^2)}{s^2}D_n(\psi)
\le\frac{276}{s^2}D_n(\psi),\qquad 0<s\le1/3.
\]

All deductions below hold with the first coefficient on 0 < s <= sqrt(2)-1. No input-complexity assumption is introduced. Compactness is used only to attain a closest product for each fixed n.

## 2. Channel representation and pure tails

Let P_{a,+/-} be the Pauli eigenprojectors and E_a(rho)=sum_{+/-} Tr(P_{a,+/-}rho) P_{a,+/-}. Let R(rho)=Tr(rho) I/2. On I, X, Y, Z, respectively, each E_a fixes I and its own Pauli matrix and kills the other two, while R fixes I and kills all three. Therefore

\[
A_s=sE_X+sE_Y+s^2E_Z+r_sR,\qquad r_s=1-2s-s^2.
\]

The weights sum to one. They are nonnegative precisely in the interval needed here, r_s >= 0 for s <= sqrt(2)-1; at 1/3, r_s=2/9. Represent the three dephasings by effects w_a P_{a,+/-} and preparations P_{a,+/-}. Represent replacement by effects r_s P_{Z,+/-} and preparation I/2. The effects sum to I and every nonzero effect has rank one. Thus this is an explicit CPTP measure-and-prepare representation of the required channel, including at the extension endpoint after deleting its zero effects.

For effect w_o |a_o><a_o| define the unnormalized tail vector eta_o=sqrt(w_o)(<a_o| tensor I)psi and p_o=||eta_o||^2. If p_o>0, chi_o=eta_o/sqrt(p_o) is a normalized pure tail state. Completeness implies

\[
\sum_o p_o=1,\qquad \rho_B=\sum_o p_oP_{\chi_o}.
\]

This does not depend on the purity of the preparation. Zero effects and outcomes with zero probability contribute zero; no division by zero is performed. Arbitrary entanglement among the remaining qubits is permitted.

## 3. SSA cancellation and the determinant budget

For any CPTP tail channel N, let T_o=N(P_{chi_o}) and let theta_o be the preparation. The output and its extension are

\[
\Omega_{QB}=\sum_op_o\theta_o\otimes T_o,
\qquad\Omega_{QBL}=\sum_op_o\theta_o\otimes T_o\otimes|o\rangle\langle o|.
\]

The Q marginal is A_s(rho_1). SSA, S(QB)+S(QL) >= S(Q)+S(QBL), gives the lower bound. Explicitly,

\[
S(QBL)=H(p)+\sum_op_o[S(\theta_o)+S(T_o)],\quad
S(QL)=H(p)+\sum_op_oS(\theta_o).
\]

Consequently

\[
S((A_s\otimes N)(P_\psi))\ge S(A_s(\rho_1))+\sum_op_oS(T_o).\tag{A}
\]

The cancellation is exact for mixed I/2 preparations as well. This is a direct application of the SSA direction used in [Shor v1, Theorem 1, equations (7)–(14)](https://arxiv.org/html/quant-ph/0201149v1); it does not improperly substitute a mixed state into his displayed pure-preparation entropy equalities.

For rho=(I+r dot sigma)/2, write u=s^2(r_x^2+r_y^2)+s^4r_z^2. Because |r|<=1 and s<1, u<=s^2. For G(u)=h((1+sqrt(u))/2), differentiation gives

\[
-G'(u)=\frac{\operatorname{atanh}\sqrt u}{2\sqrt u}\ge\frac12,
\]

with value 1/2 at zero. Hence

\[
\begin{aligned}
S(A_s(\rho))-m_s
&\ge\tfrac12(s^2-u)\\
&=\tfrac{s^2}{2}(1-|r|^2)+\tfrac{s^2(1-s^2)}2 r_z^2\\
&=2s^2\det\rho+\tfrac{s^2(1-s^2)}2 r_z^2
\ge2s^2\det\rho.\tag{B}
\end{aligned}
\]

This also proves that m_s is the one-site minimum, attained at pure equatorial states. Inserting N=A_s^{tensor(n-1)} in (A) and subtracting nm_s gives

\[
D_n(\psi)\ge2s^2\det\rho_1+\sum_op_oD_{n-1}(\chi_o).\tag{C}
\]

Set D_0=0 on the scalar pure input. Induction shows D_n>=0 and pays every conditional determinant with its probability weight. This nonnegativity follows directly here and also agrees with the pinned minimum-output additivity statement. Terminal pure one-qubit inputs have determinant zero but nonnegative latitude deficit, which can be dropped.

## 4. Exact swap identity and arbitrary-ensemble drift

Let W_j swap site j between the two copies, Sym_j=(I+W_j)/2, H=product_{j=2}^n Sym_j, and T_n=Tr(P_psi^{tensor2} product_{j=1}^n Sym_j). Put F_n=1-T_n. The test projectors have operator norm at most one. Let W_B=product_{j=2}^n W_j and W_all=W_1 W_B. Then H W_B=H. For v=psi tensor psi, W_all v=v. Since the swaps commute,

\[
\langle v,HW_1v\rangle
=\langle v,HW_BW_{\rm all}v\rangle
=\langle v,Hv\rangle.
\]

Tracing out both first-site copies in the latter expectation proves the exact identity

\[
T_n(\psi)=\operatorname{Tr}[H(\rho_B\otimes\rho_B)].\tag{D}
\]

Full-input purity is essential here; neither productness nor a pure tail marginal is assumed. For n=1, H=I on the scalar tail and (D) yields T_1=1.

Take **any** finite pure-state ensemble rho_B=sum_i p_i sigma_i, sigma_i=P_{chi_i}. Expanding the two tensor factors, using sum_i p_i=1, gives exactly

\[
\begin{aligned}
L&:=\sum_ip_i\operatorname{Tr}[H(\sigma_i\otimes\sigma_i)]
-\operatorname{Tr}[H(\rho_B\otimes\rho_B)]\\
&=\frac12\sum_{i,j}p_ip_j
\operatorname{Tr}[H((\sigma_i-\sigma_j)\otimes(\sigma_i-\sigma_j))].
\end{aligned}
\]

For each pair, trace/operator norm duality and multiplicativity of tensor-product trace norm imply an upper bound by ||sigma_i-sigma_j||_1^2. The pure-projector formula is

\[
\|\sigma_i-\sigma_j\|_1^2=4(1-\operatorname{Tr}\sigma_i\sigma_j).
\]

Thus, without any assertion that L is nonnegative,

\[
L\le2(1-\operatorname{Tr}\rho_B^2)
=2(1-\operatorname{Tr}\rho_1^2)=4\det\rho_1.\tag{E}
\]

The middle equality uses the equal nonzero Schmidt spectra of a pure bipartite state; the last uses the trace-one qubit identity 1-Tr(rho_1^2)=2 det(rho_1). Rewriting (E) gives

\[
F_n(\psi)\le\sum_ip_iF_{n-1}(\chi_i)+4\det\rho_1.\tag{F}
\]

As an additional algebraic check, write Delta_i=sigma_i-rho_B. The same L is sum_i p_i Tr(H Delta_i tensor Delta_i). For positive weights these matrices are traceless on a support of dimension at most two, because the first site is a qubit. Hence ||Delta_i||_1^2=2 Tr(Delta_i^2) and sum_i p_i Tr(Delta_i^2)=1-Tr(rho_B^2), recovering (E). This support fact is automatic and is not an input-rank restriction. The pairwise derivation above does not need it.

Choose the EB ensembles of section 2 in (F). The induction hypothesis F_{n-1} <= 2 D_{n-1}/s^2 and (C) give

\[
F_n\le\frac2{s^2}\sum_op_oD_{n-1}(\chi_o)+4\det\rho_1
\le\frac2{s^2}D_n.\tag{G}
\]

The base case F_0=0, D_0=0 is valid, as is F_1=0. This direct coefficient-one induction proves the same-tree assertion without enumerating the tree, selecting a branch, or accumulating an exponential coefficient. It never bounds D_n by a sum of the original unconditioned site impurities.

## 5. Product-test soundness: source convention and induction

In [Soleimanifar–Wright v1](https://arxiv.org/html/2201.01824v1), Definition 2 uses omega=max_product |<Phi,psi>|^2. Definitions 4–6 use exactly the projector defining T_n here. Their halved trace-distance convention need not be imported: I use only omega and Theorem 15's T_n <= 2/3+omega^2/3.

I recomputed its full induction. For ordered Schmidt probabilities lambda_i, the first-site symmetric projection gives mutually orthogonal labels on the first-site pair, with squared masses lambda_i^2 and lambda_i lambda_j (i<j). Bounding all tail outcomes except the leading diagonal branch by one gives

\[
T_n\le\lambda_1^2T_{n-1}(b_1)+\sum_{i>1}\lambda_i^2+\sum_{i<j}\lambda_i\lambda_j.
\]

Put beta=max_product |<b_1,v>|^2. The inductive bound makes the right side exactly

\[
\frac23+\frac{(\lambda_1\beta)^2}{3}
-\frac13\sum_{i>1}(\lambda_1-\lambda_i)\lambda_i
-\frac13\sum_{1<i<j}\lambda_i\lambda_j.
\]

Both subtractions are nonnegative, and lambda_1 beta<=omega by the product candidate a_1 tensor v. The base case has omega=T_1=1. This verifies Theorem 15's convention and inequality. The source's phrase calling its probability mu the vector's two-norm is read as squared two-norm, as its displayed masses require; this harmless wording does not affect the proof.

For epsilon=1-omega, the source bound now gives

\[
F_n\ge\tfrac13(1-\omega^2)\ge\tfrac13\epsilon,
\qquad\epsilon\le\frac6{s^2}D_n.\tag{H}
\]

For fixed n the product unit spheres are compact, so some pure product Phi attains omega. No uniform estimate is obtained from compactness itself.

## 6. Actual pinned amplitude branch and the separate tree

I read the actual family-276 wrapper and complete output, thermal, partners, and special files, checking them against fresh immutable raw bytes and exact-path Git blobs. The pinned results are stipulated true. The relevant statement is output.tex `lem:partner-branch` / `eq:partner-branch`, specialized to N=A_s^{tensor(n-1)}; `eq:recursion` retains the same inequality before any population-convexity averaging. It allows arbitrary normalized, nonorthogonal pure branch vectors and arbitrary zero-weight choices. The weaker final original-site population bound is not substituted for this branch statement.

At gamma=1-s^2, nu=1/2, the source channel has the required Bloch multipliers and its completed-square determinant is

\[
a(p)=\frac{1-s^2}{4}+(1-s^2)s^2(p-1/2)^2,
\quad e(p)=g(a(p)),\quad e(1/2)=m_s.
\]

One-step subtraction of nm_s yields

\[
D_n(\psi)\ge e(p)-m_s+(1-p)D_{n-1}(\psi_0)+pD_{n-1}(\psi_1).
\]

Inductively retaining the conditional populations, rather than averaging them first, gives

\[
D_n(\psi)\ge\sum_{v:\,|v|<n}q(v)[e(p_v)-m_s],
\]

where q(v) is the computational prefix probability and p_v is its conditional next-bit probability. Only positive-probability prefixes are used. The actual thermal statement covers deterministic branches.

Direct differentiation gives g'(a)=2 atanh(sqrt(1-4a))/sqrt(1-4a)>=2, with its limiting value at 1/4. Therefore

\[
e(p)-m_s\ge2(1-s^2)s^2(p-1/2)^2.
\]

For b(p)=KL(Bern(p)||Bern(1/2)), log r<=r-1 gives

\[
b(p)\le\sum_{i=0}^1 p_i(2p_i-1)=4(p-1/2)^2,
\]

including endpoints by continuity. The classical chain rule follows by factoring q(x) into its conditional bit probabilities and taking the q expectation of log(q(x)/2^{-n}). Consequently

\[
D_n\ge c_s\sum_vq(v)b(p_v)=c_s\operatorname{KL}(q\|u_n),
\qquad c_s=\frac{(1-s^2)s^2}{2}>0.\tag{I}
\]

This proves exactly the needed amplitude estimate without importing any prior I280 proof verdict. The computational tree here differs from the EB tree in (G). Each yields a bound on the same original D_n; only those completed scalar bounds are combined later. No coupling of branches is assumed and no sum of the two lower bounds on D_n is asserted.

## 7. Full-law Hellinger rounding and all constants

Take a closest product Phi from (H). Write p(x)=|<x,Phi>|^2 and q(x)=|<x,psi>|^2. Round each local factor of Phi to equal magnitudes, preserving the phases of its two coefficients, to obtain an equatorial product hatPhi. At a pole assign the missing phase arbitrarily. Multiplying the nonnegative local inner products gives

\[
|\langle\Phi,\widehat\Phi\rangle|=a:=\sum_x\sqrt{p(x)u_n(x)}.
\]

For Hellinger squared distance H^2(f,g)=sum_x(sqrt(f(x))-sqrt(g(x)))^2, choose a global phase on psi maximizing its real overlap with Phi. Taking coordinate moduli cannot increase Euclidean distance, hence

\[
H^2(p,q)\le2(1-\sqrt{1-\epsilon})\le2\epsilon.
\]

For b=sum_x sqrt(q(x)u_n(x)), concavity of log on the q-support gives

\[
\log b\ge\sum_{q(x)>0}q(x)\log\sqrt{u_n(x)/q(x)}
=-\tfrac12\operatorname{KL}(q\|u_n).
\]

All ratios here are positive and finite. Thus H^2(q,u_n)=2(1-b)<=KL(q||u_n)<=D_n/c_s. The Euclidean triangle inequality, squared using (x+y)^2<=2x^2+2y^2, yields

\[
H^2(p,u_n)\le4\epsilon+2D_n/c_s.
\]

For pure projectors ||P_v-P_w||_1^2=4(1-|<v,w>|^2). Since 0<=a<=1,

\[
\|P_\Phi-P_{\widehat\Phi}\|_1^2
=4(1-a^2)\le8(1-a)=4H^2(p,u_n)
\le16\epsilon+8D_n/c_s.
\]

The trace-norm triangle inequality, again squared with coefficient two, then gives

\[
\begin{aligned}
\|P_\psi-P_{\widehat\Phi}\|_1^2
&\le2(4\epsilon)+2(16\epsilon+8D_n/c_s)\\
&=40\epsilon+16D_n/c_s\\
&\le\frac{240+32/(1-s^2)}{s^2}D_n.
\end{aligned}
\]

Taking the equatorial-product infimum only decreases this quantity. For s<=1/3, 1-s^2>=8/9, so 240+32/(1-s^2)<=240+36=276. There is no hidden halving of distance or log-base factor. These are separate upper bounds by D_n used together; the proof does not spend D_n as if its lower bounds were additive.

## 8. Boundary audit and final disposition

- **Zero and deterministic outcomes:** omit zero-probability terms in both trees. Assigning arbitrary normalized vectors to zero-weight branches changes no entropy, ensemble, test, or KL term. KL against uniform remains finite even for laws with zeros.
- **Empty tails and n=1:** D_0=F_0=0, T_0=1. Every pure one-qubit input has F_1=epsilon=0 and D_1>=0. Latitude correction still follows from (I). More directly, if z is its Bloch latitude, the equatorial infimum is 2(1-sqrt(1-z^2)), consistent with the proof.
- **Poles:** missing local phases are freely chosen, and the local overlap with the rounded equatorial state is 1/sqrt(2). The full affinity identity remains exact. A single pole has equatorial squared distance 2 and D_1=h((1+s^2)/2)-h((1+s)/2)>0.
- **D_n=0:** (H) forces psi to be product; (I) forces q=u_n. Its product factors therefore each have equal computational magnitudes, so psi is an equatorial product exactly.
- **s=1/3:** replacement weight 2/9, c_s=4/81, and the unsimplified numerator is exactly 276. Both inequalities include this endpoint.
- **s=sqrt(2)-1:** replacement weight zero is omitted; the remaining rank-one effects still sum to I. All derivative, entropy, and KL estimates retain positive coefficients. The extension numerator is 256+16 sqrt(2); the frozen claim correctly extends only the unsimplified bound.
- **s approaching zero:** s=0 is excluded. For a pole D_1=s^2/2+O(s^4), so the required divergence of any uniform coefficient is consistent with this statement. No claim for non-EB parameters is made.

The frozen original proof has no fatal gap, unresolved proof obligation, or necessary mathematical repair. The shared author/parent bridge survives independent recomputation. Verdict **PASS**, with the same-proof extension also **PASS** under its stated unsimplified constant. This says nothing about a separate contribution gate or acceptance.
