# r130 working notes (durable; append-only in spirit)

Runner: Factory Droid, model Opus 5.5 (claude-opus-5-5), high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## 0. Reading order (as it happened)
1. AGENTS.md; research-brief-2026-10-20.txt; fresh-analytic-r130-brief.txt (full).
2. r129 REPORT.md, packet/public/report.md, screens.md, reading-limits.md (full; screens.md middle shown truncated by terminal), discovery-analytic-r129-parent/intake.json (full).
3. sources/upstream.json; NEW-TEN-2026-10-14.md lines 1-80 (acceptance rules); CONTENTS.md family titles (all 372) and catalogue entries for 071,072,073,080,085,088,092,093,119,139,140,146,147,213,214,232,237,239,261,335,347.
4. Stale navigation-only family-history counts: fresh-arithmetic-discovery-r95/packet/private/history/family-history-counts.txt (analytic rows). Zero-count analytic families: 071, 072, 146, 147, 214, 232, 323, 335, 347.
5. Family 213 screen: fetched and authenticated all 11 tex files of the quasi-transitive paper; read main.tex and introduction.tex in full. History hits: i72 (lines 54-66), r117 operation-comparison line 5. Site-percolation-on-all-quasi-transitive extension would need re-running the full ~100-page proof (two-cluster bound across an edge has no site analogue: adjacent open sites share a cluster). No black-box reduction site->bond exists. Dropped as infeasible for a full proof in-round; antecedent SiteCriticality2026 treats Z^d.
6. Family 072 (zero history): fetched and authenticated all tex bodies of both papers. Read in full: Brennan paper 00-introduction, 00-history, 01-preliminaries, 02-weighted-law, 03-escape, 04-critical-pairing, 05-transport; companion 00-introduction, 03-escape, 05-strict-transport, 06-equality-barrier.

## 1. The source mechanism, with a free exponent s>0 (weight |Q_F|^s = |F'|^{-s}, t=-s)

Operator L_s = (A_{-1/2+i/2}+A_{1/2+i/2})/2 with A_z Phi(F) = |Q_F(z)|^s Phi(T_zF).
Disk comparison (Brennan Prop. prop:disk-transfer, verbatim with B_E^s): M_{-s}[f'](r) <= C ||L_s^n||, 2^{-n} ~ 1-r.
So B_S(-s) <= beta_s := log_2 rho_s.

Law (Brennan Lemma lem:weighted-law): eigenmeasure exists for any rho>0; horizontal period needs
 ||mu A_{2+i}-mu|| <= C rho^{-n} v v^{-s} = C (2^{s-1}/rho)^n -> 0, i.e. beta > s-1.
For s in (0,2) and beta >= s^2/4 this holds because s^2/4-(s-1)=(s/2-1)^2>0.
Then E[|Q_F(z)|^s Phi(T_zF)] = y^{-beta} E Phi(F).

Moments (differentiate E|Q_F(x+iy)|^s = y^{-beta} at i):
 d_y|Q|^s = (s a/y)|Q|^s ; Delta |Q|^s = s^2 |Q'/Q|^2 |Q|^s.
 => E a = -beta/s,  E|q|^2 = beta(beta+1)/s^2.

Potential V = y^k/|F-xi|. Critical points G_F = F - (iy/k)F' = xi; V = k y^{k-1}|Q| there.
Transport weight y^{beta-1}|Q|^{s+2} must equal (V/k)^{s+2}: forces (k-1)(s+2) = beta-1,
 k = (beta+s+1)/(s+2).
Escape area tail: test |F(z^#)|^{-m}; Jacobian matching forces m=s+2; deterministic bound
 int_{|w|>=1/16} |w|^{-(s+2)} dA < infinity iff s>0. Submean gives y^{(beta+s+1)/(s+2)}/|F| -> 0,
 i.e. exactly the same k. Real-axis covering needs 2k-1 = (2beta+s)/(s+2) > 0: automatic for s>0.

Jacobian: k^2 J = k(k-1) + (2k-1) a + |q|^2 (Brennan lem:jacobian-moments, s-free). Then
 s^2 (s+2)^2 k^2 E J(i) = s^2(beta+s+1)(beta-1) - s(s+2)(2beta+s)beta + (s+2)^2 beta(beta+1)
                       = 4beta^2 + (4+4s-s^2) beta - s^2(s+1)
                       = (4 beta - s^2)(beta + s + 1).
(Checked by hand expansion: beta^2 coefficient s^2-2s(s+2)+(s+2)^2 = 4; beta coefficient
 s^3 - s^2(s+2) + (s+2)^2 = -s^2+4s+4; constant -s^2(s+1).)
Checks: s=2 gives 4(beta-1)(beta+3)/(16*... ) ~ k(k-1)>0 iff beta>1 (Brennan); s=1 gives
 (4beta-1)(beta+2)/9 (companion threshold 1/4). 

Equality case beta = s^2/4: k = (s+2)/4 in (1/2,1). J==0 means |q+(2k-1)/2| = 1/2, so
 |q| >= 1-k = (2-s)/4 > 0, and the companion's harmonic barrier (lem:no-zero-J) applies verbatim
 with log 4 replaced by log(1/(1-k)).

CONCLUSION S1 (author screen): for every t in (-2,0), there are eps>0, C with
 M_t[f'](r) <= C (1-r)^{-t^2/4+eps} for all f in S, 1/2<=r<1; hence B_S(t) < t^2/4 on (-2,0),
 and B_S(t) <= t^2/4 gives B_S'(-2) = -1 (B convex, B = |t|-1 left of -2).
Every step is the printed source mechanism with the exponent left free. Only new item is the
factorization (4beta-s^2)(beta+s+1). This is a parameter substitution in a printed proof;
by the brief's lesson it is technical. NOT frozen, NOT nominated.

Convexity alone does NOT give it: from B(-2)=1, B(-1)<1/4, B(0)=0 one gets only
B < (3|t|-2)/4 on [-2,-1] and B < |t|/4 on [-1,0]; both exceed t^2/4 in the interior.

## 2. Positive exponents t in (0, 6-4sqrt2) (s=-t<0): where the substitution breaks
- Moments: E a = beta/t, E|q|^2 = beta(beta+1)/t^2; E k^2 J proportional to (4beta-t^2)(beta+1-t): still positive for beta>t^2/4.
- Period: |F'|^t <= C v^{-3t}: need beta > 3t-1, true if beta>=t^2/4 and t<6-4sqrt2.
- BREAK 1: area tail needs int_{|w|>c}|w|^{-(2-t)} dA < inf: false for t>=0 (unbounded images in K, e.g. F(z)=z-i).
- BREAK 2: k=(beta+1-t)/(2-t) equals (2-t)/4 < 1/2 at beta=t^2/4: the real-axis covering sum of h^{2k-1} diverges.
  Bad targets are boundary points xi with omega(B(xi,r)) >= r^{1/k} infinitely often (1/k>2). If dOmega has positive
  area such points can fill positive area (since int omega(B(xi,r)) dA(xi) = pi r^2). So the positive side needs a
  genuinely new statement: under the eigen-law, a.s. the bad-target set has zero area. Unknown.
- Literature caution (memory, not read): Hedenmalm (Bloch functions, asymptotic variance, zero packing) Sigma^2<1
  together with Ivrii's B(t) ~ Sigma^2 t^2/4 would already give B(t)<t^2/4 for tiny |t|. Not verified; no claim made.

## 3. Primary-literature check (2026-10-20): the family-072 extension is preempted
- WebSearch "Hedenmalm asymptotic variance Bloch functions universal integral means spectrum Kraetzer conjecture
  Sigma^2 < 1" returned arXiv:2610.23853.
- FetchUrl https://arxiv.org/html/2610.23853 -> v1 [math.CV] 16 Oct 2026, I. Binder, O. Ivrii, I. Prause, S. Smirnov,
  "Brennan's Conjecture and the Universal Integral Means Spectrum". Read extent: whole HTML rendering returned
  (abstract, sections 1.1-1.4, section 2 (2.1-2.3) and the reference list).
- Stated Theorem: B_b(t) <= t^2/4 on [-2,2], strict on ]-2,2[ \ {0}; via Makarov's identity B = max(B_b, 3t-1),
  B(t) < t^2/4 on ]-2, 6-4sqrt2[ \ {0}. Full argument written only for the NON-strict inequality; strictness is
  announced via a perturbed weight (their eq. (6)) and "averaged positivity", details deferred to a separate paper.
- Their deterministic proof: potential V_xi = s^k/|f-xi|, s=1-|z|^2, G = f + s f'/(2k zbar), T = |z| s^{k-1}/|f'|,
  q=2-t, k>q/4, b=(k-1)q > -1; index-theorem signed area sum_{G=xi} T^q sgn det DG <= 0; radial identity (23)
  absorbs all f''/f' terms into a boundary term; localization by psi = 1_Delta handles t>0; letting k -> q/4 gives
  beta_phi(t) <= t^2/4 for bounded univalent phi. This bypasses both of my positive-side BREAKs (no eigen-law, no
  area tail, no real-axis covering).
- Consequence for r130: S1 (strict on (-2,0)) is inside their announced theorem and its non-strict version inside
  their written proof; the positive side t in (0, 6-4sqrt2) (non-strict) is inside their written proof. Nothing of
  the 072 extension direction is unclaimed in the literature. What remains unwritten anywhere I read is a complete
  proof of STRICTNESS for t in (0,2); that is announced by experts (novelty limit) and needs a quantitative excess of
  maxima over saddles (a barrier with averaging) for which I have no argument. Not frozen.
- Project-history grep (no-ignore, hidden; excluded forbidden rounds and own root) for 2610.23853 / Binder..Ivrii /
  Prause / "reborn proof": no project-history hit other than jin-v13 (an i135 external source mentioning Prause).
  So this preemption appears new to project records.
- Endpoint note: at t=-2 (q=4) the BIPS identity needs k>1; the coefficient 4r^2-q/k becomes 4r^2-4<0 at k=1, so
  the i135 logarithmic endpoint is not an immediate corollary; a gauge s*L(s) keeps log V superharmonic near the
  boundary but makes the coefficient 4(r^2-1)+O(1/log) of indefinite sign. Not pursued (r128/i135 territory).

## 4. Decision
PREFREEZE. No nominee. Families screened in depth: 213 (dropped: needs full rerun), 072 (S1 technical and
externally preempted; strict positive side announced by BIPS and unproved here).
