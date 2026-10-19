# T082C109: unresolved endpoint-count target

Original author research prose, CC BY 4.0. This is an unresolved research archive, not a theorem nomination, independent review, or contribution rating. No acceptance count or gate is assigned.

## Frozen scope and outcome

The exact target remains [frozen-target.md](frozen-target.md), with SHA256 `d587244ce220b4764f9a31c723753bc752084a985a1b141369e6f06df97b014a`. It asks for an absolute, logarithm-free bound

\[
 \|S_n(F,G)\|_{3/2}\le C\sqrt n\|F\|_3\|G\|_3
\]

for all complex inputs in \(L^3(\mathbb R^2)\), all integers \(n\ge1\), and the pointwise supremum over at most \(n\) disjoint radius intervals with rational endpoints. The endpoint choices may depend on the output. No restricted substitute has been adopted.

No complete proof or counterexample to that target was obtained. Two plausible attempts can be ruled out by explicit arguments below. Those arguments only diagnose proposed proof mechanisms; they are not a substantial new theorem claim. The strongest primary comparison supplies more than its headline statement, but still does not close the required endpoint. No formalization, independent review, or publication is requested for this packet.

## Stipulated operations and the exact missing estimate

All statements and operative proofs in the pinned OpenAI source at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The principal source is *Annular variation of the triangular Hilbert transform at the symmetric point*, October 5, 2026 (source082). Its `thm:count` already proves precisely this counting estimate with an additional \(\log(2+n)\). Its companions on the dyadic triangular Hilbert form and maximal triangular Hilbert transform were compared at their operative interfaces; this report does not audit them.

The annular source already supplies all of the following:

1. `prop:smooth-switches` pays \(\sqrt n\) for smooth annuli with output-dependent switches, using the cubic matrix energy and a norm rescaling. Thus choosing many intervals, linearizing their absolute values, and handling complex phases are paid.
2. The hard/smooth identity writes the smooth annular kernel as
   \[
   I_{e,R}=c_0\,\mathbf1_{e<|t|<R}/t+E_e-E_R,
   \qquad c_0=2g_3''(0)=-2/(3\sqrt{6\pi})\ne0.
   \]
   Here \(g_s(t)=(2\pi s)^{-1/2}e^{-t^2/(2s)}\), \(P(v)=2\int_0^v(-g_3'''(u))du\), and
   \[
   E_\rho(t)=\{P(|t|/\rho)-c_0\mathbf1_{|t|>\rho}\}/t.
   \]
   Each endpoint kernel has actual jumps, despite its Gaussian tails.
3. `prop:endpoint-errors` groups comparable radii. Disjointness makes paired endpoint lengths summable and leaves at most two unpaired endpoints per scale. It gives uniform Gaussian bounds away from the jumps. Groups with more than \(\sqrt n\) endpoints are few and are paid by the maximal envelope. Smooth first-moment removal and its geometric telescoping are also paid.
4. `prop:rough-family`, `prop:frequency-block`, and `cor:frequency-continuum` estimate the remaining groups. The total jump count is \(O(n)\), the individual count is \(O(\sqrt n)\), and each normalized frequency block costs \(O(\sqrt n)\). A polynomial frequency cutoff leaves a bounded remainder. Summing \(O(\log(2+n))\) blocks creates the stated logarithm.

The exact remaining task can be stated without a stronger auxiliary conjecture: replace the bound in `prop:endpoint-errors` by \(C\sqrt n\prod_{v=0}^2\|G_v\|_3\), with its full printed output-dependent interval and coefficient quantifiers. The source's hard/smooth identity, paid smooth estimate, duality and countable-supremum completion then prove the frozen target. Conversely the target, together with the smooth estimate, bounds these same endpoint-error forms. Thus this is the unpaid operation, not merely a convenient sufficient strengthening. Finite-valued step choices are the source's initial interface; its completion operations pass to the frozen measurable supremum.

Nothing in this reduction itself establishes substantiality. A successful solution would still need a fresh comparison against the existing operations and primary literature. The target is not nominated just because it removes a conspicuous logarithm.

## Attempt 1: merging all frequency blocks fails its coefficient contract

Here is a precise obstruction to one tempting direct use of the source's frequency-continuum estimate. It does **not** obstruct every possible all-frequency estimate.

Fix any positive Gaussian parameter \(q\). Consider the compactly supported real odd kernel

\[
 K(z)=\operatorname{sgn}(z)\left[\mathbf1_{1<|z|<2}
                    -\frac35\mathbf1_{2<|z|<3}\right].
\]

The zeroth and second moments vanish by oddness, and the first moment is
\[
2\left(\frac{2^2-1^2}{2}-\frac35\frac{3^2-2^2}{2}\right)=0.
\]
It has six nonzero jumps at \(\pm1,\pm2,\pm3\), is constant elsewhere, and satisfies the rough-family envelope with fixed constants, for example \(c=1,A\ge e^9\). A single scale with \(m=6,n=36\) satisfies the count hypotheses. Thus this is an admissible example for the proposed general rough-family summation.

Set
\[
 U(z)=\tfrac12\int_{-\infty}^{z}(z-u)^2K(u)du,
 \qquad f=U/g_{3q},\qquad w=f'''.
\]
The three moment conditions make \(U\) compactly supported: to the right of the support its defining polynomial has all three coefficients zero. It is \(C^2\), piecewise smooth, and \(U'''=K\) almost everywhere. The same statements hold for \(f\). The function \(w\) is compactly supported and piecewise smooth. At each jump point \(z_j\),
\[
 a_j=w(z_j+)-w(z_j-)=\frac{K(z_j+)-K(z_j-)}{g_{3q}(z_j)}\ne0.
\]
Indeed, all lower-derivative terms in differentiating \(U/g_{3q}\) are continuous there. Distributionally,
\[
 w'=r+\sum_j a_j\delta_{z_j},
\]
where \(r\) is a compactly supported piecewise smooth function of bounded variation.

Use \(\widehat h(\xi)=(2\pi)^{-1}\int h(z)e^{-i\xi z}dz\). Integration by parts on the finitely many smooth pieces gives \(\widehat r(\xi)=O(|\xi|^{-1})\); hence
\[
 \widehat w(\xi)=\frac{1}{2\pi i\xi}\sum_j a_je^{-i\xi z_j}
                         +O(|\xi|^{-2}).
\]
Squaring and integrating yields
\[
 \int_1^M\xi|\widehat w(\xi)|^2d\xi
   =\frac{\sum_j|a_j|^2}{4\pi^2}\log M+O(1).
\]
For completeness, each off-diagonal term is a constant multiple of
\(\int_1^M e^{-i(z_j-z_l)\xi}d\xi/\xi\), uniformly bounded for \(j\ne l\) by integration by parts; the remainder after squaring has integrable size \(O(\xi^{-2})\). The positive diagonal coefficient is nonzero.

Since \(\widehat w=(i\xi)^3\widehat f\), let \(D=2^j\) and \(\Xi_D=\{D\le|\xi|<2D\}\). Up to fixed positive multiplicative constants,
\[
 \sum_{D\le M}\int_{\Xi_D}|D^4\widehat f(\xi)|^2\frac{d\xi}{D}
 =\sum_{D\le M}D^7\int_{\Xi_D}|\widehat f(\xi)|^2d\xi
 \asymp\int_{1\le|\xi|<2M}|\xi||\widehat w(\xi)|^2d\xi
 \asymp\log M.
\]
Here the asymptotic comparability is for dyadic \(M\) sufficiently large. Each coefficient family \(\mu=D^4\widehat f/\sqrt n\) individually fits the source's block normalization, but their combined square budget diverges, even for this fixed \(n\). A cutoff equal to one on an expanding interior frequency range retains this obstruction.

There is a second paid-contract issue: the block proof chooses row heat variance \(\theta s\) with \(\theta=1/(16D^2)\). Its normalized measure \(d\xi/D\) has bounded mass on one block. Summing infinitely many blocks repeats the unchanged-edge initial energy on infinite total mass. Choosing the smallest common variance does not preserve the low-frequency derivative estimates with the original normalization. Neither issue is addressed by merely changing the order of integration.

This is a failure of this proposed uniform coefficient-budget argument, **not** a lower bound for the bilinear operator or the frozen \(S_n\). In particular it does not contradict the source's finite-cutoff proof, its logarithmic bound, or the possibility of a new cancellation exploiting the special endpoint family. The compact example belongs to the general rough-family class; it is not asserted to have exactly the special endpoint form.

## Attempt 2: a raw derivative square estimate is false

The standard separation into long and short variations suggests controlling short-radius variation by a square integral of derivatives. It is essential to retain cancellation at this step. The following more elementary bound, which would discard that cancellation, is false:
\[
 \left\|\left(\int_0^1
 |F(x+t,y)G(x,y+t)-F(x-t,y)G(x,y-t)|^2\frac{dt}{t}\right)^{1/2}\right\|_{3/2}
 \lesssim\|F\|_3\|G\|_3.
\]

Choose a smooth compactly supported \(\eta\) equal to one on \([-1,1]\), and put
\(F_N(x,y)=e^{iNx}\eta(x)\eta(y)\),
\(G(x,y)=\eta(x)\eta(y)\).
Their \(L^3\) norms are independent of \(N\). On \(Q=[-1/4,1/4]^2\), for \(0<t<1/4\), the difference in the display is
\(2i e^{iNx}\sin(Nt)\). For \(N\ge8\) the square of the displayed inner quantity is at least
\[
 4\int_{1/N}^{1/4}\sin^2(Nt)\frac{dt}{t}
 =2\log N+O(1).
\]
The error is bounded uniformly because \(\int_1^A\cos(2u)du/u\) is uniformly bounded by integration by parts. The \(L^{3/2}\) norm on the fixed positive-measure square \(Q\) therefore grows at least as a positive constant times \(\sqrt{\log N}\). This disproves precisely the displayed auxiliary bound. It does not disprove short variation itself: integrating oscillation before taking absolute values can be substantially smaller than this derivative square majorant.

## Strongest existing primary reduction examined

The primary comparisons below concern actual proofs, not just theorem headlines. Exact private files, hashes, versions and semantic ranges are in the retrieval receipt and reading ledger.

* Jones–Seeger–Wright, *Strong variational and jump inequalities in harmonic analysis*, author-hosted draft, Lemma 1.3 and §6/Lemma 6.1: long/short separation and the Besov/linear frequency-square-function method. The relevant proof uses linear Littlewood–Paley control. Its applicability to the triangular bilinear endpoint is not supplied by its scalar sequence decomposition. [Author PDF](https://people.math.wisc.edu/~aseeger/papers/jsw.pdf).
* Durcik–Kovač–Škreb–Thiele, *Norm-variation of ergodic averages with respect to two commuting transformations*, arXiv:1603.00631v3: Theorem 2, Corollary 3, Proposition 7, Lemmas 9–10, and §2.4. The printed norm-variation theorem has a fixed partition outside the norm; it is not the output-adaptive target here. However, Lemmas 9–10 explicitly bound **pointwise short variation**, and the sharp-indicator decomposition in §2.4 has summable shifted-bump losses. Its estimate \(C_2^{1/4}C_3^{1/4}\), with \(C_2\sim2^{k(2-\lambda)}\), \(C_3\sim2^{k(1-\lambda)}\), \(\lambda=5/4\), gives \(2^{k/8}\) for negative \(k\). Combining that proof with the pointwise short-variation lemma also handles the sharp cutoff at the same \(L^4\times L^4\to L^2\) exponents. Claiming that only smooth cutoffs are paid would overlook this compatible composition. Complex inputs follow by real and imaginary decomposition with an absolute factor. [Version 3 PDF](https://arxiv.org/pdf/1603.00631v3).
* Mirek–Stein–Zorin-Kranich, *Jump inequalities via real interpolation*, arXiv:1808.04592v3, Lemma 2.7 and its proof: the jump quasi-norm is equivalent to a real-interpolation norm involving \(L^\infty(V^\infty)\) and \(L^{\theta p,\theta q}(V^{\theta\rho})\). For the desired jump exponent \(\rho=2\), this requires a suitable decomposition with variation exponent \(2\theta<2\). A bound for every variation exponent greater than two does not automatically provide that decomposition. Also its jump quasi-norm keeps the supremum in the jump threshold outside the spatial norm; that distinction must be retained. Version 2 was initially retrieved, but version 3's actual lemma and proof were checked for the operative comparison. [Version 3 PDF](https://arxiv.org/pdf/1808.04592v3).

These comparisons expose two separate missing interfaces. The sharp short-variation mechanism in the bilinear primary proof is real, but its square expansion uses \(L^4\) input control; no \(L^3\times L^3\to L^{3/2}\) endpoint replacement was established. Moreover, short variation alone does not settle the whole output-adaptive endpoint-error count: the compatible long-scale contribution must also be controlled. Even an improved estimate at exponent four, interpolated with a logarithmic exponent-three bound, would retain a positive logarithmic power at interior exponents and does not improve the endpoint three itself. This is not a proof that other interpolation or endpoint methods cannot work.

The source's smooth matrix calculus and the primary bilinear short-variation calculus therefore cannot simply be declared incompatible forever, nor declared composable at the desired endpoint without a proof. The missing mixed-scale, output-dependent estimate remains explicit and unproved.

## Limits and handoff

This archive establishes only the two elementary failures of attempted estimates and the contract comparison. It does not establish priority, global literature exhaustion, an obstruction to the target, or a new contribution eligible for acceptance. No independent correctness or contribution gate has occurred. The target's original bytes and full quantifiers are preserved.

The packet keeps original prose/code under `public/`; copied upstream and third-party PDF/text evidence remains under `private/` with original rights. The inventory verifier certifies bytes and scope only. Publication, uploads, shared index changes, commits, and nested agent work were not performed.
