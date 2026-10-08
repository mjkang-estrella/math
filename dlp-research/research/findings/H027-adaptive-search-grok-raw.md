# H027 differential adaptive walks — raw Grok proposals

2026-10-08. Received via task_status; unverified proposer report. Complete-cost and distinguished-point review is pending. Not an accepted improvement.

Verified gain is **NONE**. The square-root reference is unchanged. These are three executable low-memory hypotheses. They are not a survey, and they are not claims that a cheaper step has already been measured.

All three stay on an ordinary curve \(E/\mathbb{F}_p\) with \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), and \(\mathrm{Aut}=\{\pm1\}\). The scalar \(k\) is full range. Inputs are public \(E,G,Q=[k]G\). No advice, no secret range, no special endomorphism, and no binary-field halving.

The low-memory comparator is negation rho: about \(0.886\sqrt{q}\) batched affine additions at \(5M+S\). High-memory x-only interleaved BSGS, about \(2.5M+S\) per stored key and about \(0.62\) of rho's field work at \(S/M=1\), is not the target. Distinguished-point storage here is \(q^{1/4}\), under the \(0.19\sqrt{q}\) line. Setup is \(O(\log q)\) and is not in the leading term.

H023's pair \((x(P),x(P-G))\) updates by translation by \(G\) in \(2M+I\), batched limit \(5M\) with no squaring, and that ordered pair determines \(P\). The same note shows that memoryless \(\pm G\) on the reflection quotient only walks a path with cycles of length at most \(2\). These cards do not use that canonical \(\pm G\) rule as the rho function. They keep the oriented pair, hash only the canonical abscissa, and insert an unbounded mixer so the stride bound of the H025 screen does not apply. Inversions are amortized across parallel walks, in the same limit in which rho is priced at \(5M+S\).

## Card 1 — Abscissa-bucket doubling on a differential \(+G\) fill

**Operations.** Each walker holds \((x,x_{\mathrm{prev}},a,b)\), meaning the point \(P=[a]G+[b]Q\) and \(x(P-G)\). One walker starts at \(Q\) with label \((0,1)\); the others start at known \([s_i]G+Q\). The first previous abscissa is one public addition, \(Q-G\).

Let \(\ell=32\). If the integer representative of \(x\) is nonzero mod \(\ell\), fill. The H023 identity sends the pair to \((x(P+G),x(P))\) and \((a,b)\leftarrow(a+1,b)\). If \(x\equiv 0\pmod{\ell}\), double by the two rational formulas already recorded for this pair:
\[
x(2P)=\frac{(3x^2+A)^2}{4(x(x^2+A)+B)}-2x,
\]
and the companion value \(x(2P-G)\). Labels become \((2a,2b)\). Do not sort or reflect after a fill. That sort is what collapses \(\pm G\) to length-\(2\) cycles.

Hash the canonical abscissa. A distinguished point stores \((x,a,b)\) and the walker id.

**Recovery.** An abscissa hit is \(\varepsilon_1(a_1+b_1 k)\equiv\varepsilon_2(a_2+b_2 k)\pmod q\). Try both relative signs and test
\[
k(\varepsilon_1 b_1-\varepsilon_2 b_2)\equiv\varepsilon_2 a_2-\varepsilon_1 a_1.
\]
Cross hits against a pure-\(G\) walker have coefficient \(\pm 2^{e}\neq 0\). A same-depth hit with both coefficients zero is discarded and the walk continues. A surviving candidate is checked by one scalar multiplication. If the step cap \(4\sqrt{q}\) is reached, fall back to a full x-only BSGS and charge it.

**Why this can be cheaper.** The samples are mostly fixed-difference translations at \(5M\), against rho's \(5M+S\). Doubling is rational in the pair, so there is no square root and no \(y\). It is also what keeps the walk off a single arithmetic progression: H025's \(O(sL)\) relation count is for bounded strides and does not include doubling. Density \(\delta=1/32\) gives the batched average
\[
\frac{31}{32}\cdot 5M+\frac{1}{32}(11M+3S)=5.1875M+0.09375S.
\]
At \(S/M=1\) that is \(5.281\) against rho's \(6\), about \(12\%\) fewer field units per emitted abscissa. Canonical-\(x\) equality still identifies \(\pm P\), so the negation identification is in the key. The oriented state is not claimed to be a uniform random walk after the bucket choice.

**Baseline and predicted complete-work gain.** If the number of emitted abscissae up to the first useful hit is at most the negation-rho count \(0.886\sqrt{q}\), ledger work is about \(0.88\) of rho, a \(12\%\) saving, low memory. Break-even is about \(13.6\%\) more samples than that count (about \(1.006\sqrt{q}\) samples). This does not beat high-memory x-only BSGS. Verified gain: none.

**Other costs.** Setup is the curve constants plus one addition per start. Memory is \(q^{1/4}\) distinguished keys. Failures are zero denominators (known points \(\pm G\), restart that walker), zero \(k\)-coefficients, and the BSGS fallback. No hidden advice. Field additions, hashes, and distinguished-point integer arithmetic are outside the ledger, as they are for rho. Finite herds must be charged the same \((I-3M)/W\) remainder on both sides.

**Prior art read.** H023 fixed-difference walk, including the \(5M\) batch limit, the length-\(\le 2\) quotient cycles, and both doubling formulas (this session). H025 bounded-stride screen (this session). Bernstein–Lange–Schwabe negation and fruitless cycles, from the 2011 slides and the 2011/003 abstract in search text; the PDF itself did not load. Baseline constants and the H019 \(2.5M+S\) comparator are project memory, not a new PDF pass. Doubling inside rho is older than this card; the Galbraith–Gaudry survey snippet and the Bos thesis \(r\)-adding notes say mixed doubling walks are already used. The new piece is the \(5M\) fill between those doublings.

**Unsupported premise.** Cross-walker canonical-abscissa hits still arrive by \(0.886\sqrt{q}\) emitted points. Structure of the \(+G\) runs, or the bucket rule, may delay the first useful hit by more than \(13.6\%\). That is a measured collision count, not a postulate that the adaptive walk is uniform.

**Cheapest falsifier.** One ordinary prime-order curve with \(q\approx 2^{16}\), \(\ell=32\), \(64\) parallel walkers, cap \(4\sqrt{q}\) fills-plus-doubles, \(32\) declared seeds. Log emitted abscissae, doubling counts, and whether the recovered \(k\) matches. Kill the saving if the median useful-hit count exceeds \(1.006\sqrt{q}\), or if mean count times \(5.281\) meets or exceeds \(0.886\sqrt{q}\cdot 6\). Do not retune \(\ell\) after seeing the hits.

## Card 2 — Same fill, with a Tonelli jump that moves the \(Q\)-coefficient

Card 1's coefficient of \(k\) is a difference of powers of \(2\). This card uses the same \(5M\) fill, but the mixer is a precomputed Teske jump \(J_h=c_h G+d_h Q\) with \(d_h\neq 0\), so both label coordinates move by large amounts.

**Operations.** Fill as in Card 1 for \(r=\lceil 4\log_2 q\rceil\) steps. Then recover \(y\) from the current abscissa by a square root, using the stored \(x(P-G)\) only to choose the sign: H023's uniqueness statement says exactly one square root matches the previous abscissa. Add the precomputed \(J_h\) and add \(-G\), both with the known \(y(J_h)\), and restart the pair at \((x(P+J_h),x(P+J_h-G))\). Labels add \((c_h,d_h)\). The index \(h\) is the abscissa mod \(16\), fixed before the macro, not a proximity-to-table rule.

**Recovery.** Same signed linear equation as Card 1. A jump with \(d_h\neq 0\) makes \(b_1-\varepsilon b_2\equiv 0\) an \(O(1/q)\) event rather than a pure 2-power collision. Discard those hits and continue.

**Predicted ledger.** A \(p\equiv 3\pmod 4\) square root is one exponentiation, charged as \(1.5\log_2 q\) multiplications-or-squarings. Two full additions are \(2(5M+S)\). Divided by \(r=4\log_2 q\), the large-\(q\) cost per sample tends to \(5.375M\)-equivalents at \(S/M=1\), against \(6\). That is about \(10\%\) if the sample count matches rho, with room for about \(12\%\) more samples. At \(q\approx 2^{16}\) and \(r=64\) the same model is \(5.56\), only about \(7\%\) before a harder square root. For \(p\equiv 1\pmod 4\), Tonelli–Shanks can be worse; the prediction does not use \(1.5\log_2 q\) there.

**Applicability and costs.** Same ordinary full-range scope. Memory and fallback match Card 1. The square root and both reseed additions are charged on every macro, including macros that produce no hit. No advice.

**Prior art read.** Same H023 uniqueness and translation formulas (this session). Teske \(r\)-adding and the Bos thesis additive-walk description, from the thesis excerpt in search text, not a full-thesis pass. Bernstein–Lange–Schwabe as in Card 1. This is not Zhang–Wang halving (binary fields only; search snippet, not used).

**Unsupported premise.** Amortized square-root cost really is \(O(\log q)\) with a leading factor small enough to leave a gap, and an arithmetic progression of length \(4\log_2 q\) between jumps does not cut the useful-hit rate by more than the slack above. Choosing \(h\) from \(x\) does not make the next points uniform.

**Cheapest falsifier.** Same \(q\approx 2^{16}\) curve, but require \(p\equiv 3\pmod 4\) so the square root is one exponentiation. Use \(r=64\), \(16\) jump table entries, \(32\) seeds, cap \(4\sqrt{q}\). Instrument square-root multiplications separately from fills. Kill if total charged \(M\)-equivalents to the first verified hit are at least the negation-rho control on that same curve and the same walker count. A second prime with \(p\equiv 1\pmod 4\) is a different test; do not treat a pass on \(p\equiv 3\pmod 4\) as covering it.

## Card 3 — Tripling reset, same fill, independent of the doubling graph

If the map \(P\mapsto[2]P\) has an unusually poor functional graph, Card 1 can lose its sample slack while a cube map does not. This card never doubles.

**Operations.** Fill exactly as in Card 1. On the bucket \(x\equiv 0\pmod{\ell}$, \(\ell=32\), replace the pair by \((x(3P),x(3P-G))\) and set \((a,b)\leftarrow(3a,3b)\). All four quantities are rational, with no square root:

- \(x(P+G)\) by the H023 translation of the current pair.
- \(x(2P)\) by the duplication formula.
- \(x(3P)=\Sigma(x(2P),x(P))-x(P)\).
- \(x(3P-G)=\Sigma(x(2P),x(P-G))-x(P+G)\).

Here \(\Sigma(x_A,x_B)\) is the usual rational sum of abscissae
\[
x(A+B)+x(A-B)=\frac{2(x_A+x_B)(x_A x_B+A)+4B}{(x_A-x_B)^2}.
\]
The identity \(2P-(P-G)=P+G\) fixes the second line. Author tally, not an accepted project ledger: \(12M+4S+4I\) serial, about \(24M+4S\) after four inverses are amortized at \(3M\) each. A reviewer can collapse denominators; until then the card uses \(24M+4S\).

**Recovery.** The same signed equation. The coefficient of \(k\) is a difference of powers of \(3\), nonzero unless the two depths and signs match. Discard that null hit.

**Predicted gain.** At density \(1/32\) and \(S/M=1\),
\[
\frac{31}{32}\cdot 5+\frac{1}{32}\cdot 28=5.719
\]
against \(6\), about \(4.7\%\), and only about \(5\%\) slack on the sample count. If the four-inverse tally is high, this card ties or loses even when the collision count matches rho. It is the independent dynamical control for Card 1, not a second copy of the same saving.

**Costs.** Same scope, memory, fallback, and setup as Card 1. Every tripling is charged, including wasted ones. No advice.

**Prior art read.** H023 translation and the duplication formula (this session). The \(\Sigma\) identity is the standard differential sum used to avoid a \(y\)-coordinate; Bernstein's differential-addition-chain note (search text of the 2006 note) is about known-scalar chains on a Montgomery model, which these curves do not have. It is not a license for this search schedule.

**Unsupported premise.** The tripling bucket produces a first useful abscissa hit within \(5\%\) of the negation-rho sample count, and the four-inverse cost is not missing further multiplications. No claim that a degree-\(9\) tripling map is random after the bucket selection.

**Cheapest falsifier.** Re-derive the tripling operation count on paper before any run. If the audited batched cost at \(\delta=1/32\) is already at least \(5M+S\), kill the card with no curve computation. If the tally still beats \(5M+S\), run the Card 1 falsifier with tripling in place of doubling and kill it when measured ledger work meets the rho control.

## What these are not

They are not the H026 fixed-depth shared-jump tree, not an all-pairs novelty scan, and not a nearest-abscissa walk. A pure \(\pm G\) rule on the reflection quotient is already a path of 2-cycles; density \(1/32\) does not repair that rule, which is why the state here stays oriented. They are not H025's fixed signed layouts, and they are not EDS or character normalizations. No coordinate class was closed by a degree or generic-group bound.
