# H035 independent Grok proposals — retained raw report

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h035-independent-fullwork-grok-20261008-r1`

Completed, no pending children. Independent initial proposal role withheld H035
fusion findings. Reviewer conclusions are qualified in H035-independent-disposition.md.

No survivor. Under this lens nothing distinct is worth a solver test: the three exact-representation or fusion shapes that still look open lose on a complete ledger to the paired schedule at \(2.5M+S+3A\) per abscissa. I did not read H035 proposals.

Comparators are the high-memory interleaved negation schedule, average \((2\sqrt{2}/3)\sqrt{q}\approx 0.943\sqrt{q}\) keys, and low-memory negation rho at about \(0.886\sqrt{q}\) steps of \(5M+S\). A full addition is \(5M+S\) once Montgomery’s \(3M\) inversion share is included. Any trick the paired \(\pm\) schedule can copy does not change the ratio.

## 1. Unreduced chord fractions

Skip the inverse and store the exact fraction for each side abscissa. For center \(C\) and offset \(U\), with \(d_x=x(C)-x(U)\), \(d_y^\pm=y(C)\mp y(U)\) and \(\sigma=x(C)+x(U)\),

\[
x(C\pm U)=\frac{N_\pm}{D},\qquad N_\pm=(d_y^\pm)^2-\sigma\, d_x^2,\qquad D=d_x^2.
\]

Per \(\pm\) pair that is \(1M+3S+6A\) and no inverse, against the reference pair \(5M+2S+6A\). Kernel saving: \(2M-0.5S\) per key. Additions tie. Center updates are unchanged, because \(x(C)\) and \(y(C)\) are still required.

Exact equality is \(N_1D_2=N_2D_1\). Hashing the reduced abscissa puts the inverse back and adds an extra half-square per key. A sorted or tree detector therefore pays \(2M+A\) per comparison. Insertion against \(t\) stored keys costs \(2\log_2 t\) multiplications per key. The kernel saving wins only if

\[
\log_2 t<1-0.25s\le 1\qquad(s=S/M\in[0,1]),
\]

so \(t<2\). Every table that stores two or more keys loses. A window scan of \(w\ge 1\) stored fractions costs at least \(2M\) and already spends the saving. Memory holds two field elements per key; at a matched peak the baby count halves and \(b+q/(4b)\) moves from \(\sqrt{q}\) to \(1.25\sqrt{q}\).

Prior art is Montgomery batching plus ordinary fraction comparison, not a new group law. The unsupported assumption was that an exact quotient order costs less than about two field multiplications. It does not, in the field-operation ledger or at bit complexity (inversion is already a small constant times multiplication, which is why the share is \(3M\)).

Applicability: any single-target BSGS or rho table with \(t\ge 2\), any prime field, either memory regime. Predicted complete gain: negative for every \(t\ge 2\).

## 2. One inverse serving more than the \(\pm\) pair

The \(1.5M\) inversion share is \(3M\) for one denominator \(x(C)-x(U)\), split across two slopes. A third key at that same denominator would drop the share below \(1.5M\).

For fixed offset \(U\) and fixed \(\delta\in\mathbb{F}_p\),

\[
x(P)-x(U)-\delta=0
\]

has degree 2, so at most two points \(P\). Those two are a negation pair \(\{P,-P\}\) whenever both exist. Their sums with \(U\) are \(P+U\) and \(-P+U\), whose abscissae are exactly \(x(P\pm U)\). That is the reference pair, not a third sum. Bundle size 2 is therefore the maximum, and it is already used.

Accidental equality of denominators across different offsets is a 3SUM-type condition on the lists. It is not a schedule of identical denominators growing with the batch, and the expected number in a batch of \(k\) random differences is \(\binom{k}{2}/p\to 0\).

Prior art is the same paired-slope inverse the reference already charges. Unsupported assumption: some \(n>2\) useful abscissae share one exact denominator. The degree-2 count discharges it for every ordinary Weierstrass curve. No curve run.

Applicability: full-range prime order, any offset table. Predicted complete gain: none. The inversion term cannot fall below the reference share.

## 3. A third abscissa fused out of the same chord

From the same \(d=(x(C)-x(U))^{-1}\) the two slopes determine the doubling abscissa of the center by the differential identity, with \(\alpha=x(C+U)\), \(\beta=x(C-U)\) and public \(\gamma=x(2U)\):

\[
x(2C)=\frac{2(\alpha+\beta)(\alpha\beta+A)+4B}{(\alpha-\beta)^2}-\gamma.
\]

The new denominator \((\alpha-\beta)^2\) is not \(d\). Forming it costs a new inversion share \(3M\), one square, and at least one multiply: \(\ge 4M+S\) for that key, above \(2.5M+S+3A\). The label is \(2c\). Those even indices already sit on an arithmetic progression the reference can emit directly at \(2.5M+S+3A\). Paying \(4M+S\) to reprint them is a loss, and a geometric subsequence is not a new collision image.

The same bound hits the tangent: \(1/(2y(C))\) is a different denominator. Co-Z history does not remove it. With a common scale \(x=X/Z\), \(y=Y/Z\),

\[
\lambda=\frac{Y_1-Y_2}{X_1-X_2},\qquad X_{\mathrm{new}}=\lambda^2 Z-(X_1+X_2),
\]

the \(Z\) cancels in \(\lambda\) and the difference \(X_1-X_2\) is still inverted. Keeping every intermediate \((X:Z)\) and comparing across steps is mechanism 1 again.

Prior art is the chord-and-tangent law plus co-Z rescaling (Meloni). Unsupported assumption: the third intersection, or a common-\(Z\) representative, is a new labelled abscissa at marginal cost below one reference key. The extra denominator kills it before coverage is counted.

Applicability: prime order, so no rational \(2\)-torsion and no Montgomery/Edwards/Hessian shortcut (those need a rational point of order \(2\), \(3\), or \(4\); an \(\mathbb{F}_p\)-isogeny preserves that absence when \(q>4\sqrt{p}\)). Predicted complete gain: negative wherever the reference limit applies.

## Why the nearby coverage escape also fails

The signed-pair floor \((2/3)\sqrt{q}\) is only a factor \(\sqrt{2}\) fewer keys than \(0.943\sqrt{q}\). Reaching it with full additions costs

\[
\frac{5+s}{\sqrt{2}\,(2.5+s)}\ge 1.21
\]

times the reference field work on \(s\in[0,1]\). The two-addition parabola already loses with inversions given away. Cheap \(x\)-only emission produces arithmetic progressions, whose same-role sums are \(O(t)\) rather than injective \(t^2\) images. A set with injective pairwise sums is not generated by repeated translation at this kernel price.

Nothing here changes exponent \(1/2\) or the verified-improvement mark. No experiment, file edit, or further primitive is justified on these three shapes.
