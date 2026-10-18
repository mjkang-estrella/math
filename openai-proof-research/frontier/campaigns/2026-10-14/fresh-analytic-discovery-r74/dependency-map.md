# Full-scope author proof dependency map

Read candidate-proof.md first. The following modules form one proof, not
separately nominated lemmas. All statuses here are author claims only.
Historical notes and copied author snapshots retain their original conditional
wording; the unified proof supplies the ordering and resolves those premises.

| Step | Needed conclusion | Detailed proof / exact antecedent | Prior inputs |
|---|---|---|---|
| C1 | Open circuits, cap moments, conditional uniqueness | cap-author-cap-core.md §§1–2 | iid finite nonatomic originals, fixed M |
| C2 | Exact equality of all bigeodesics | cap-author-cap-core.md §3 | C1, K>=2ML |
| C3 | Every rooted cap ray eventually uncapped; finite cap influence | cap-author-cap-core.md §§4,6 | C1 and path coercivity; no rooted reattachment |
| M | Local continuity, coercivity, finite lengths, ordinary/extended norm shape | cap-author-shape-and-length.md §§1–6; cap-shape-interface.md fixed-event addition | C1, iid low-cost path count |
| E | Uniform random-slope cocycle linearity on nonergodic extensions | stationary-extension-cocycle.md; parent-author-extension-cocycle-linearity.md | M, stationary additive cocycle bounded by cap metric |
| D | Coalescing reference graph and selected-reference stability | dh-limiting-coupling.md; cubic-wall.md | C1,C3,M; DH actual A2' pre-coalescence construction |
| O | Ordered extremal labels and downward density contradiction | ah-6-8-integration.md; same-status-lowering.md | D,M, exact one-edge same-status kernel; actual AH6–8 proofs |
| S | Upward extremal selector preservation and coalescence | label-stability-interface.md including symmetry, squeezing, isolated labels, no-return; cubic-wall.md | D,O,M,E; actual AH9.2,9.7–9.9,9.11 |
| A | Simultaneous all-ray cap classification, fixed-functional uniqueness/backwards finiteness | ah-9-10-integration.md | S,O,M; actual AH10 and AH4.5 |
| P | Opposite exceptional coalescence | parent-author-halfplane-transfer.md; source03–04 deterministic/Borel arguments | A,M,C1 coding tail; independent splice of both originals and cap auxiliaries |
| B | Finite expected usable edge-label counts and no forks | parent-author-status-preserving-perturbations.md; source05–06 | A,P; reversible same-status one-edge kernel |
| T | Arbitrary cap gains, shared union preservation, distinct marked labels | same parent note; source07 | B,A; status-preserving product tilt and full-output posterior |
| Z | Contradiction p/8<=ell W_I/m for every m | candidate-proof.md §7; source08 | T and source05 deterministic label budget |
| F | Full original no-bigeodesics target | C2 plus Z | no original moments, no fixed direction |

Important nondependencies: optional original-ray-to-cap-tail and endpoint
B(x) comparisons are not used to infer M or A. No uniform original shape,
original Busemann linearity, iid cap law, cap upward finite energy, or
nonergodic-extension mixing is assumed. Source charts use D4 lattice
isometries; diagonal wall coordinates are an explicit separate construction.

The byte verifier certifies none of this mathematics. interface-checker.py
checks seven finite cases/groups only. The proof and contribution gates must
be fresh and independent; no favorable gate is included in this packet.
