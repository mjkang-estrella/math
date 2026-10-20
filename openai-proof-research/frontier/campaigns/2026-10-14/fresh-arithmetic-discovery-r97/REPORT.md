# Arithmetic r97 handoff

PREFREEZE: no frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned.

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Main direction: family 009, noninjective compatible maps of mod-$p$ Milnor $K$-theory

The mod-$p$ reconstruction source was read in full (sections 01-05). r24 had left the noninjective case open, with the gap "classify collapsed plane configurations, then build a valuation with exponent-$p$ value groups".

Proved here (elementary, in `packet/public/report.md`):

- **Proposition A ($p=2$).** For any field $K$ of characteristic 2 and $L$ as in the source, a linear $\theta:V_K\to V_L$ is compatible exactly when it maps each $K^2$-projective line into an $L^2$-projective line or to a point. So for $p=2$ the collapse problem disappears at the level of lines.
- **Proposition B (all $p$).** Every valuation $v$ on $K$, field homomorphism $\beta:\kappa_v\to L$ and linear extension over $K^\times/(1+\mathfrak m_v)K^{\times p}$ gives a compatible map. This covers r24's examples and pure value-group maps with nondegenerate image.
- **Lemma C.** Nondegenerate image contains a quadrangle.
- An explicit odd-$p$ collapse: with a discrete valuation, every source affine configuration at a uniformizer has monomial image, so `prop:intersection` cannot start there.

Strongest reduction: for $p=2$ the classification reduces to a place theorem. A collinearity-preserving group homomorphism $\mathbb P_{K^2}(K)\to\mathbb P_{L^2}(L)$ whose image contains a quadrangle should come from a valuation. The unpaid operation is building that valuation ring from collinearity and the group law, a Carter-Vogt type result for two different coordinate fields. Lineation literature was located but not read, and rigid-element and Efrat-diameter attempts recover at most the value-group layer. For odd $p$ a collapse classification is needed first. Not frozen.

Also screened: the base-free reading of `thm:main` (all fields with $p^2\le[F:F^p]<\infty$) follows by reading the source proofs with weaker hypotheses. It is TECHNICAL and was not frozen. Family 004 over number fields would rerun every central input; not frozen. History-only families are listed in `packet/public/screens.md`.

Novelty: nothing here is claimed new to the literature.

## Inventory

- 7 retained pinned 009 source files, all read and blob-checked against the complete preprints tree; none removed.
- No primary literature; navigation items in `external-navigation.json`.
- 9 unchanged history copies (both briefs, r96 handoff files, r24 screen-009, r73 reading-and-credit).

## Seal

`FINAL.json` binds this outside report, the manifest, the verifier, the controls script and the public report. Take its detached hash from the parent handoff. Run the read-only verifier and the copied controls as described in `packet/public/reproduction.md`. `integrity-results.json` is written outside the packet and must be hashed separately. These artifact checks are not mathematical gates.
