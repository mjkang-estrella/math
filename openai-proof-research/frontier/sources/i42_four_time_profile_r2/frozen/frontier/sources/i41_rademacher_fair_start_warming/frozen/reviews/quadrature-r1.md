# Quadrature: adversarial review, round 1

**Verdict: ACCEPT as a correct downstream corollary of the accepted pinned source. No substantive proof correction is required. New-to-literature priority is not established, and the analytic mechanism and endpoint obstruction should not be presented as new.**

Reviewed `proposals/quadrature.md` on 2026-10-08, under `AGENTS.md`. This is a fresh review with no prior findings. All pinned OpenAI theorems are accepted as instructed; this review checks their statements and the deductions, not their upstream proofs.

## 1. Source and dependency check

`sources/upstream.json` pins OpenAI/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I checked the family 017 entry in `sources/CONTENTS.md`, its paths in the complete `sources/preprints-tree.json`, and the actual manuscript sources.

The relevant source is [build/sections/series.tex, Corollary `series:generalized`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/series.tex), lines 90–97. Its hypotheses are fixed real \(a,b>0\), angles in radians, and its conclusion is precisely convergence of

\[
\sum_{k\ge1}k^{-a}|\sin k|^{-b}
\quad\Longleftrightarrow\quad a>\max\{1,b\}.
\]

Thus \(a=2s,b=2\) is an authorized application. In particular, the strict boundary is part of the cited statement. Also checked [build/main.tex, Theorem `thm:main` and the introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex). The latter records the ineffective nature of the approximation threshold, so the proposal appropriately makes no effective-constant claim.

The family catalogue lists one manuscript for family 017, not a separate companion. Its introduction and series section already state the generalized series theorem, but do not state this Sobolev quadrature corollary. The catalogue/path check did not identify a family 017 companion duplicating it. This is a bounded duplicate check, not a claim to have searched the text of all 719 manuscripts.

## 2. Mathematical validation

### Domain and quantifiers

The theorem's range \(s>1/2\) is essential and is stated correctly. With normalized Haar measure on \(\mathbb T=\mathbb R/\mathbb Z\) and Fourier convention \(e_k(t)=e^{2\pi ikt}\),

\[
\sum_k|\widehat f(k)|
\le \|f\|_{H^s}\left(\sum_k(1+k^2)^{-s}\right)^{1/2}<\infty.
\]

This supplies the continuous representative and bounded point evaluation directly. The mean is \(\widehat f(0)\). No almost-everywhere evaluation issue remains.

The positive assertion means \(\forall s>1\;\exists C_s\;\forall N,x,f\). The negative assertion means \(\forall s\in(1/2,1]\;\forall x\;\exists f\in H^s(\mathbb T;\mathbb R)\) with unbounded unnormalized errors. The proof establishes exactly these quantifiers: \(f\) may depend on \(s,x\), but is fixed as \(N\) varies. It need not provide a single \(f\) simultaneously for all \(x\), and the theorem does not claim that.

### Normalization and use of the series theorem

For \(\alpha=1/\pi\),

\[
d_k=e^{2\pi ik\alpha}-1=e^{2ik}-1,
\qquad |d_k|=2|\sin k|.
\]

There is no missing \(\pi\), reciprocal, or factor of two. For \(k\ge1\),

\[
2^{-s}k^{-2s}\le(1+k^2)^{-s}\le k^{-2s},
\qquad
S_s=\frac12\sum_{k\ge1}(1+k^2)^{-s}|\sin k|^{-2}.
\]

Therefore the cited theorem gives exactly \(S_s<\infty\iff s>1\).

### Sufficiency

Cauchy–Schwarz gives

\[
\sum_{k\ne0}\left|\frac{\widehat f(k)}{d_k}\right|
\le\left(\sum_{k\ne0}(1+k^2)^s|\widehat f(k)|^2\right)^{1/2}\sqrt{S_s}.
\]

Thus the asserted transfer function \(u\) has an absolutely and uniformly convergent Fourier series. Termwise translation is legitimate; the Fourier coefficients of \(u(\cdot+\alpha)-u\) equal those of \(f\). Uniqueness of Fourier coefficients for continuous functions proves the equality everywhere. Telescoping then proves the bound with \(2\sqrt{S_s}\), uniformly in both \(N\) and \(x\). Removing the constant coefficient is an orthogonal projection of norm one. This part is complete.

### Exact Hilbert dual norm

For fixed \(N,x\), put

\[
c_{N,k}=e^{2\pi ikx}\sum_{j=0}^{N-1}e^{2\pi ikj\alpha}
=e^{2\pi ikx}\frac{e^{2\pi ikN\alpha}-1}{d_k}
\quad(k\ne0),\qquad c_{N,0}=0.
\]

Then \(A_N(f)=\sum_k c_{N,k}\widehat f(k)\). Since \(|c_{N,k}|\le N\), the weighted dual sequence is square summable for each fixed \(N\), even when \(S_s=\infty\). Consequently

\[
\|A_N\|^2=\sum_{k\ne0}(1+k^2)^{-s}|c_{N,k}|^2,
\]

as claimed. Equality, rather than merely an upper bound, follows by taking Fourier coefficients proportional to \((1+k^2)^{-s}\overline{c_{N,k}}\). This sequence belongs to \(H^s\). It also has conjugate symmetry, so the same norm can be attained on the real Hilbert space. There is no lost \(\sqrt2\) from the positive and negative frequencies. Independence of \(x\) is exact.

### Necessity: the finite-frequency Cesàro argument is sound

Write \(a_k=(1+k^2)^{-s}/|d_k|^2\). If \(\sup_N\|A_N\|\le C\), then for each finite \(F\subset\mathbb Z\setminus\{0\}\),

\[
\frac1M\sum_{N=1}^M\sum_{k\in F}a_k|e^{2\pi ikN\alpha}-1|^2\le C^2.
\]

For each \(k\ne0\), irrationality implies \(e^{2\pi ik\alpha}\ne1\); the finite geometric sum gives a Cesàro limit of zero for the exponential. Taking the limit in this *finite* sum yields

\[
2\sum_{k\in F}a_k\le C^2.
\]

Only now exhaust the nonzero integers by finite sets. Positivity gives \(S_s\le C^2/2\). This does not exchange a limit with an infinite, possibly divergent series. The argument rules out bounded norms at \(s=1\) as well as below it.

### Fixed real function

For \(s>1/2\), every \(A_N\) is a bounded linear functional on the complete space \(H^s\). The contrapositive of uniform boundedness therefore gives one \(f\) with \(\sup_N|A_N(f)|=\infty\). If \(f=g+ih\), both \(g,h\) are real members of \(H^s\), and \(A_N(f)=A_N(g)+iA_N(h)\). If both real sequences were bounded, the complex sequence would be bounded. Thus at least one is the required real counterexample. Equivalently, apply uniform boundedness directly on the real space using the preceding norm computation. The counterexample may be made zero mean without changing its errors.

## 3. Novelty assessment and literature check

The exact general principle established by this proof is, for any irrational \(\alpha\) and \(s>1/2\),

\[
\sup_{N,x}N\|Q_{N,x}-I\|_{(H^s)^*}<\infty
\quad\Longleftrightarrow\quad
\sum_{k\ne0}\frac{(1+k^2)^{-s}}{|e^{2\pi ik\alpha}-1|^2}<\infty.
\]

This is an elementary Fourier/functional-analysis criterion. Applying the newly accepted arithmetic input at \(1/\pi\) is a useful exact corollary, but does not introduce a new quadrature construction or a new transference technique.

In particular, **the failure at \(s\le1\) does not need any new theorem about \(\pi\)**. For the convergent denominators \(q_j\) of any irrational \(\alpha\),

\[
|e^{2\pi iq_j\alpha}-1|\le2\pi\|q_j\alpha\|<2\pi/q_j.
\]

The corresponding summands in the general criterion are bounded below by a positive constant times \(q_j^{2-2s}\). They fail to tend to zero for \(s\le1\). The norm/Cesàro/uniform-boundedness argument consequently gives the same fixed-function obstruction for every irrational rotation. The new arithmetic content is the positive conclusion for this particular angle arbitrarily close to \(s=1\).

Primary literature checked:

* Leonardo Colzani, [*Speed of convergence of Weyl sums over Kronecker sequences*](https://link.springer.com/article/10.1007/s00605-022-01785-z), Monatshefte für Mathematik 200 (2023), 209–228, published online 2022. Theorems 1–2 concern fixed-function, almost-everywhere-in-angle estimates; the proof uses the same geometric Fourier multiplier. Remark 15 explicitly discusses norm-uniform \(C/N\) estimates under Diophantine and smoothness hypotheses. These establish that the framework is existing bounded-remainder theory. The metric statements do not settle a prescribed angle \(1/\pi\), nor do they permit exchanging the function and exceptional-angle quantifiers. I did not find the proposal's precise fixed-angle Sobolev threshold stated there.
* Josef Dick, Friedrich Pillichshammer, Kosuke Suzuki, Mario Ullrich, and Takehito Yoshiki, [*Lattice-based integration algorithms: Kronecker sequences and rank-1 lattices*](https://link.springer.com/article/10.1007/s10231-017-0670-3), Annali di Matematica Pura ed Applicata 197 (2018), 109–126. Section 4.1 uses nodes \((n/N,\{n\alpha_1\},\ldots)\), with homogeneous-boundary function spaces and mixed smoothness. Its lattice results are relevant context but are not a direct duplicate of this one-dimensional periodic rule for all initial-segment lengths. One cannot infer a contradiction or priority resolution from the phrase “Kronecker lattice.”
* Dick and Pillichshammer, [*Periodic functions with bounded remainder*](https://www.dmg.tuwien.ac.at/nfn/DP05b_accepted.pdf), Archiv der Mathematik 87 (2006), 554–563. The stated sharp Fourier-decay results concern van der Corput sequences, not this rotation or this Hilbert norm. Likewise Hellekalek and Larcher, [*On functions with bounded remainder*](https://www.numdam.org/article/AIF_1989__39_1_17_0.pdf), Annales de l'Institut Fourier 39 (1989), 17–26, specialize their main results to \(q\)-adic transformations. These titles alone would be insufficient evidence of duplication.

This bounded search supports the proposal's explicit reservation about priority. It does **not** certify a new-to-literature theorem. The honest description is “a sharp Sobolev quadrature corollary for the newly controlled angle \(1/\pi\), using classical bounded-remainder methods.” Its substantive downstream value is a full worst-case operator statement and a fixed-real-function failure statement, with the arithmetic input separated cleanly.

## 4. Nonblocking improvements

1. At proposal lines 64–65, replace the ambiguous “every such sum would be \(\le C^2/2\)” by the displayed conclusion \(\sum_{k\in F}(1+k^2)^{-s}/|d_k|^2\le C^2/2\). The Cesàro-averaged numerator sum itself is bounded by \(C^2\), not \(C^2/2\). The intended argument is already correct.
2. Add the elementary fixed-\(N\) estimate \(|c_{N,k}|\le N\) when explaining the exact dual norm. This makes clear why that norm series is finite even in the divergent-small-divisor regime.
3. In the novelty paragraph, explicitly identify the endpoint obstruction as angle-independent and add the Colzani citation. Retain the reservation that priority has not been established. “Newly available explicit angle” would be more precise as “newly available sharp arithmetic control of this explicit angle.”
4. Preserve the evaluation range \(1/2<s\le1\) in any summary of failure. The proposition does not formulate a point-evaluation rule on arbitrary \(H^s\) equivalence classes below that range. Also, “sharp” concerns the regularity threshold, not an optimal numerical constant.

Validation was analytic: direct source-statement verification, exact Fourier/dual calculations, the finite-set limit argument, and the Banach-space counterexample. No numerical convergence experiment is needed or would validate the endpoint. Only this assigned review file was written; no proposal edits, commits, or subagents were used.
