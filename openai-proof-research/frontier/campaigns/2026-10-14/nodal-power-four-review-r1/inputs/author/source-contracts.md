# Source contracts (r13)

Author: Myeongjin Kang (no affiliation). Original prose: CC BY 4.0.

Pinned upstream: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
(`sources/upstream.json`). Files were retrieved from
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/<path>`
into `inputs/pinned/`. Each local copy's Git blob SHA-1 and size equal the
entry in the complete `sources/preprints-tree.json` (31 of 31; see
`git-identities.json`). Theorems are accepted as true, per AGENTS.md.

## [P] Power-law violations of Yau's nodal upper bound (family 350)

Path: `preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/`

| Item used | File, lines | How used |
|---|---|---|
| Theorem 1.1 (fixed power loss on $S^4\times S^1$); "no assertion in dimensions three or four" | sections/introduction.tex 28–48 | target gap; T4 is the dimension-four case |
| eq:weighted-operator, eq:hessian-test, $\delta=10^{-6}$ | sections/framework.tex 5–60 | notation, rerun on $S^3$ |
| eq:round-beam, def:certificate, prop:step | sections/framework.tex 65–156 | rerun on $S^3$ (candidate Section 9) |
| lem:seed | sections/envelopes.tex 16–91 | re-proved on $S^3$ (candidate Lemma 3.1) |
| eq:preparation; lem:corrugation; the remark "This is where base dimension four is used" | sections/envelopes.tex 96–516, esp. 383–433 | ported as candidate Lemma 5.1 with full input; identifies the only dimension-four step |
| prop:envelope | sections/envelopes.tex 520–659 | replaced by candidate Proposition 8.1 (same conclusions) |
| lem:phase-hessian, lem:polynomial-inverse, prop:packets, eq:jet-span, scaled-packet lemma | sections/waves.tex 1–708 | rerun with base dimension three (Section 9 table) |
| gluing, lem:noncancellation, lem:signs, lem:correction, lem:simplicity, prop:step proof, lem:persistence, Theorem 1.1 proof, warped circle | sections/global.tex 1–906 | rerun with base dimension three (Section 9 table) |

## [Q] Smooth counterexamples to Yau's nodal upper bound in dimensions three and four (family 350)

Path: `preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/`

| Item used | File, lines | How used |
|---|---|---|
| thm:main ($S^3$), thm:four ($S^2\times T^2$): unbounded $\mathcal H^{n-1}/\sqrt\lambda$, no power asserted | sections/introduction.tex 18–50, 166–169 | gap statement; comparison only |
| def:strict-profile, prop:profile-amplification (qualitative; thresholds depend on the profile), lem:profile-preparation (full on fraction $p_h/8$), lem:radial-corrugation | sections/s3-profiles.tex 1–330 | operation comparison for Lemma 6.1; not a proof dependency |
| strict envelope condition, uniform amplification lemma (qualitative) | sections/s4-envelopes.tex | comparison only |

## [S] Sharp nodal length on smooth surfaces (family 350)

Path: `preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/`.
Read only for the family survey (introduction.tex). It shows that the
upper bound holds in dimension two. It is not a dependency of T4.

## Proof dependencies of T4

Only [P] (framework, envelopes `lem:seed` structure, `lem:corrugation`
argument pattern, waves, global), used at base dimension three as
documented in candidate Section 9. [Q] and [S] are context only.
