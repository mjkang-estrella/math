# R037 — A uniform multiplicity floor in staircase tensor squares

**Accepted as the fifteenth substantial result of the 2026-10-14 campaign: 15/20.** This is internal acceptance relative to stipulated pinned sources and bounded primary comparison, not external journal review or a claim of worldwide priority.

For every integer m≥2, put N=m(m+1)/2 and ρ=(m,m−1,…,1). For every partition λ of N except the row and column, the ordinary complex tensor-square Kronecker multiplicity satisfies g(ρ,ρ,λ)≥m−1. Equality holds for λ=(N−1,1), so the uniform floor is sharp. The [frozen scope](../campaigns/2026-10-14/fresh-arithmetic-discovery-r38/scope205m.md) includes every m and every such λ; it asserts no symmetric-square, exterior-square, integral or modular analogue.

The separate contribution review rates the result **substantial, narrowly**: the residual contribution is the uniform quantitative evaluation through a four-exception invariant, predecessor bounds and the low-capacity Kostka estimate. I19's multiplicity recursion and max rule, I21's refinement, and classical configuration, Littlewood–Richardson and Pieri operations are credited antecedents. Parent high-capacity reasoning is author assistance. The result is new to this project; literature priority has not been demonstrated.

All independent gates passed at the unchanged scope:

- [Full proof](../campaigns/2026-10-14/t205m-proof-r1/review.md): PASS_FULL_T205M.
- [Contribution](../campaigns/2026-10-14/t205m-contribution-r1/review.md): SUBSTANTIAL; C1/C2 implemented.
- [Scoped formal support](../campaigns/2026-10-14/t205m-formal-review-r1/review.md): PASS_SCOPED_T205M.
- [Full manuscript](../campaigns/2026-10-14/t205m-manuscript-review-r1/review.md): PASS_FULL_MANUSCRIPT_T205M; no required repairs.

**The full multiplicity theorem is not formalized.** The 17 Lean declarations comprise seven support declarations and ten controls, with two definitions and fifteen theorems overall. They cover finite-poset ideal rank interpolation, ordered cuts and a two-ideal reduction. The ideal–partition correspondence, geometric no-cut condition, representation theory, configuration estimates, finite bases and full induction remain outside the formalization. The parent rebuilt the 21 selected formal files successfully with Lean 4.34.1 and pinned dependencies; compiler and dependency objects remain trusted.

The [13-page manuscript](../campaigns/2026-10-14/t205m-manuscript-v1/output/pdf/article.pdf) was read and visually checked by the parent and independent reviewer. The reviewer separately re-derived all proof branches, checked the KSS specialization with unbounded string lengths and independently recomputed finite bases and boundary cases. These finite checks support the proof; they do not establish the all-order lemmas.

The [91-file local release](../campaigns/2026-10-14/t205m-release-v2/README.md) contains 72 selected research/evidence files and excludes third-party bodies and dependency caches. Its clean-extraction PDF reproduces the reviewed bytes and its public finite verifier passes. Parent verification checks all seven gate anchors, archive/extraction integrity, fifteen deliberate bundle controls and byte-identical archive reassembly. The formal selection is unchanged from the earlier successful parent rebuild. [Release notes](../campaigns/2026-10-14/t205m-release-v2/RELEASE-NOTES.md) retain optional O1–O4 and exact reading/coverage limits; the reviewed article is unchanged.

Archive SHA256 `80a089c607aef4212d7f926a3d868bd3e141ee1939386f8a7d5e52db8c17918f`; bundle manifest `933d5e7deb7953e9931147191061917d02f10f5e2911e3211471ca12d8433d65`; final gate `5262bfc6ffa693b1153b470f6f77c287e1582651f8ab4495a60b95c3d0263203`; release seal `010c745f14c39ecfe0b89c61ade80a8fc8ad8a1b76682f89346470899a2d42cb`. The [parent acceptance receipt](../campaigns/2026-10-14/t205m-parent/acceptance.json) records the decision after release verification. Historical preparations retain their preacceptance states.

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0; original code MIT. Uploads remain stopped. Five further substantial accepted results remain.
