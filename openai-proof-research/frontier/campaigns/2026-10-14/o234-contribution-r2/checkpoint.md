# O234 contribution/eligibility review r2 — checkpoint (not a verdict)

Reviewer: independent CONTRIBUTION/ELIGIBILITY recovery reviewer (Claude Opus 5.5), round 2. Round 1 (Grok) failed with API 402 and produced no findings; o234-parent/contribution-r1-failure.json is preserved untouched.

Anchors confirmed on disk: output-manifest.json 85f5d443...b3b, candidate.md 2f550b13...c87, original-scope.md cfb52e90...10b.
verify.py --anchor <external> exit 0 (IDENTITY_ONLY); wrong-anchor (64 zeros) exit 1 "VERIFY_REJECTED: external anchor mismatch". Captured in checks/.

Read so far: full original-scope.md, full candidate.md, README, checkpoint, prefreeze feasibility and comparison, adversarial checks, reading limits, source map, both parent briefs.

Preliminary operation map (subject to source/primary reading):
- Lemma1 (lower outliers via ordered gradients of convex symmetric expected pressure): elementary; bounded lower outliers already allowed in Fan–Wu / FMWW at high temperature.
- Lemma2 (scalar-block rank-k vs rank-one): eta-net + exp(max)<=sum exp + equal means by in-block rotation + exponential Haar concentration + union bound. Every ingredient is standard; the question is whether the bridge is a substantial new interface.
- Lemma3: adaptation of source gen:R-continuity to cap t beyond support.
- Section6: sandwich, N first then epsilon.
Next: read the source 60-general.tex operations, Husson–Ko Section 5.1, Guionnet–Maida Thm 1.6, Fan–Wu Section 5, the I149/S149/I151 history, and the campaign briefs on what counts as substantial.
(Superseded: final verdict in report.md.)

## Checkpoint 2 (after source and Husson–Ko reading)
- Source 60-general.tex (read lines 1–420 in full): the upper bound for outliers is already free from monotonicity, gen:scalar-shift, the fixed-epsilon source theorem and gen:R-continuity. The only step monotonicity can't pay is the lower bound "one spike >= epsilon N spikes - o_eps(1)". gen:counts (endpoint convexity + in-eigenspace rotation symmetry) is the source template for the author's Lemma1 ordered-derivative argument.
- Source 70-magnetic.tex lines 389–413: sum over e^{o(N)} slices -> maximum over a FIXED finite net -> concentration for every net member. This is an internal antecedent of "partition sum <= sum over net, then concentrate each member". Its net is fixed and uses fourth-moment concentration, not an exp(cN eps)-size net.
- Husson–Ko 2208.03642v2 §5.1 (lines 1596–1747): eps-net of orthonormal frames, (5.5) max over net vs sup with a constant loss, identical law at each net point by GOE invariance, exponential moment, Markov, union bound. §7.2 Lemma 7.4 (lines 2920–2935): eps-net of S^{k(N)-1}, cardinality (3/eps)^{k(N)}, exponential tail e^{-N c(eps)} for each direction, union bound with k=o(N). The author lists §5.1 but NOT §7.2; §7.2 is the closer template (sphere net of a k-dim subspace, per-direction identical law, exponential tail, union bound, k/N small).
- Preliminary view: Lemma2 = this template applied to quenched Ising pressures (with Fan–Wu/Gromov concentration and source flat-block symmetry). Leaning TECHNICAL; still to read GM, FW §5, BS, FMWW and history before deciding.
