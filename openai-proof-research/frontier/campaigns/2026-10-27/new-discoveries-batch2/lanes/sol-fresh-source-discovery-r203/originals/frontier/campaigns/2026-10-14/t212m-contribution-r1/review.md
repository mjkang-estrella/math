# T212M independent contribution/eligibility review, round 1

Role: contribution and eligibility, conditional on correctness. This is not a
proof review. It does not certify any step of the author chain. The parent
alone accepts. Accepted count stays 16/20.

## Verdict

**SUBSTANTIAL, conditional on correctness.** This is my classification for the
unchanged full target: for every nonatomic Borel law G on finite [0,infinity),
iid planar weights have almost surely no bigeodesic, simultaneously over all
bi-infinite simple paths, with no moment and no direction restriction.

The condition matters. The substance sits in four new bridges, D, W, S and P
below. If the independent proof gate rejects any of D, S or P and no repair
exists, the verdict becomes **BLOCKED**, not TECHNICAL. The parts that are
cheaply correct (cap equivalence, cap shape, same-status kernels and source
budgets) do not reach the target by themselves, and the target may not be
narrowed. W is short. If it fails, I expect a local repair rather than a change
of classification.

The verdict is at the lower end of SUBSTANTIAL. No single component is a deep
new estimate. The classification rests on an operational fact checked in §3:
every paid route stops at a stated hypothesis. Each of the three finite-energy
mechanisms (DH Section 6, AH Sections 9.2–9.10 and source04's exact splice)
fails for the only available integrable field and is replaced by a different
argument. Length and the number of combined pieces played no role.

Not DUPLICATE: no read primary source, companion, accepted item or campaign
history item proves the moment-free full-plane statement (coverage in §5).
Not INELIGIBLE: the target is the recorded prospective full scope, it is
unchanged, and its novel class is clearly separated from the source class
(see R2).

## 0. Inputs and identity

All seven externally supplied SHA256 anchors match the frozen packet
`frontier/campaigns/2026-10-14/fresh-analytic-discovery-r74/`. I read its
`verify.py` in full before running it (it reads bytes only and writes nothing).
`python3 verify.py --anchor 26a78331…6f` printed
`IDENTITY PASS: 78 files; no mathematical verdict`. That check is about bytes,
not mathematics. I did not edit any author byte.

The coauthor material is not review. This covers the three parent-author
notes, the cap and structural Astra assistance, and
`structural-author-bridges.md`. I did not read any parallel proof-review
directory. None existed under `2026-10-14/` when I listed it, and I did not
read `t212m-parent/proof-r1-brief.txt`.

## 1. What the source pays, and what remains

Source212 Theorem 1.1 (pinned `01-introduction.tex` lines 24–37) assumes that
G is nonatomic and that E[min(X1,…,X4)^2] < infinity. Lines 44–46 state that it
"does not assert the moment-free formulation". The moment enters only through
the structural input AH A1 (`02-preliminaries.tex` lines 141–145).
`08-conclusion.tex` lines 134–140 say that the perturbation argument
(sections 05–08) uses no moment. Source05 line 289 says the same for the
usable-path counts.

Damron–Hanson arXiv:1512.00804v2, Conjecture 1 (my extraction lines 54–55),
reads: "Suppose (t_e) is i.i.d. with continuous distribution. Almost surely
there are no bigeodesics in dimension two." It has no moment condition. On the
stipulated source, the full T212M target is therefore exactly this conjecture
for finite-valued laws restricted to the class not already paid:

> new class = { nonatomic G on finite [0,infinity) : E[min of four iid copies^2] = infinity }.

Every law in this class is unbounded. However, unbounded laws with a finite
minimum second moment, including all laws with a finite mean, are already
source-paid. The packet says only that bounded G is source-paid, which
understates the source (see R2).

## 2. Ledger: paid inputs, classical inputs and new steps

| Step (dependency-map id) | Classification | Basis |
|---|---|---|
| Source05–08 budgets, edge-label count, fork exclusion, tilt density, L^2/total-variation control, full-output posterior, shared union, label telescope, final `Mq<=lW` | PAID (source) | Read source08 conclusion; operations credited in the packet. |
| Source03 charts, source04 countability, Borel and independent-exceptional argument | PAID (source) | Only the cut-transfer *statement* fails for caps (see P). |
| Peierls and dual-path counting, annulus circuits, circuit-arc shortcut | CLASSICAL | ADH Appendix C, Lemma C.5 and (26) (read in full); Cox–Durrett/Kesten contours as described by Cerf–Théret, extracted lines 247–262. |
| C1–C3: cubic cap, exact equality of bigeodesic sets, eventual uncapping, finite influence | TECHNICAL alone | Deterministic circuit surgery. New as a packaging, but each line is classical. |
| M: cap shape, coercivity, lengths | PAID in substance; the in-packet proof is redundant | The cap satisfies A2(i)–(iii). AH §3.1 (extracted lines 380–393) and DH lines 165–176 state the shape theorem under A2, through Boivin. Boivin's body is unread by me and by the authors. |
| E: random-slope cocycle linearity on nonergodic extensions | TECHNICAL | Two-sided Birkhoff, Borel–Cantelli and good-center density. |
| DH Section 3 averaging, Propositions 5.1–5.2, Theorem 5.3, Corollary 4.7 | PAID by statement under A2′ | The cap is ergodic, D4-symmetric, has all moments, a bounded shape, and unique passage times. DH A1′/A2′ at lines 275–277. |
| DH Lemma 6.2 and the triple extraction | PAID by proof only | Section 6 assumes upward finite energy (UFE) for its entirety (line 1350). I read lines 1375–1470: the proofs use only shape geometry, stationarity and the ergodic theorem, not UFE. |
| AH 4.4–4.5, 5.3–5.6, 6–8 (except 8.6), 9.1–9.4, 9.11–9.13, 10 | PAID by proof only | AH's standing hypothesis is A1 or A2, and A2 includes (v). The packet's use-site maps are consistent with every explicit energy use I found (lines 1713, 1952, 2158–2166, 2476–2485). |
| O: AH 8.6 by a same-status one-edge kernel | TECHNICAL | Given the statuses and V, the cap is a conditionally independent field. A same-status resample is AH's own one-edge argument. |
| B, T, Z: two-status source05–07 kernels | TECHNICAL | Same conditional-product observation; the formulas are the source's, split by status. |
| **D**: dominated lifted DH coupling, plus stability of selected uncapped limiting rays, replacing DH Lemma 6.6/UFE | **NEW, load-bearing** | Density domination `r^{-|F|}` of lifted line-graph laws, tight cap influence, no-return boxes, strict uncapping margins and a Fatou passage. |
| **W**: cubic wall and cheap outer circuit, axis and diagonal | NEW, short | A transplant of AH 9.10 Case 1 (lines 2470–2490) and ADH C.5. The cubic exponent turns original closures into a cap ceiling `>=8Mm^3` against an `O(m^2)` bypass. |
| **S**: AH 9.5–9.9 for the original-coordinate coupling (common good sites from marginal densities, symmetric transfer, squeeze, isolated labels, no-return selector preservation) | **NEW, load-bearing** | AH's P0 coupling is replaced by a non-stationary coupling whose cap-change set is random. |
| **P**: half-plane transfer by splicing (t,V), with a sublinear changed-vertex barrier | **NEW, load-bearing** | Source04 needs exact shared half-plane weights, and caps of a splice do not have them. |
| Final step (C2 plus Z) | Bookkeeping | Exact equality of bigeodesic sets. |

## 3. Operational test: is there a black-box route?

I looked for a route from paid results to the target that uses no new bridge.
None exists, and each obstruction is concrete.

**(a) Original iid metric.** The original metric has finite energy but no metric
regularity. Kesten's theorem, as quoted by Cerf–Théret arXiv:1404.4539v2
(extracted lines 236–246, necessity sentence at line 245), says that E[min(t_1,…,t_{2d})^d] < infinity is necessary
for the almost-sure shape theorem. In d=2 this is exactly the source's
condition. On the new class, the original metric therefore has no a.s.
uniform shape theorem. The structural inputs of AH, DH and the source all rest
on that theorem (AH §3.1 and eq. (3); the source's uniform Busemann
linearity). So AH and DH cannot be applied to t under any relabeling.

Cerf–Théret's regularized times and Cox–Durrett contours restore a shape
theorem. They do not supply Busemann or label theory, and none of the
literature I read builds structural geodesic theory on them.

**(b) Integrable surrogate.** The cap s satisfies DH A2′ and AH A2(i)–(iv) and
(vi). It provably fails upward finite energy, both DH Definition 1.9 and AH
A2(v). This is my independent check:

- For g ≠ e, the status of g is visible in s: s_g ≤ M exactly when t_g ≤ M,
  because K_g ≥ 1000M.
- A circuit that strictly encloses both endpoints of e cannot contain e. So
  L_e is a function of s_{−e}.
- Hence s_e ≤ M(L_e(s_{−e})^3+1) almost surely, given s_{−e}.
- Take λ = 1001M+1. Then P(s_e ≥ λ) > 0 under unbounded G.
- On the positive-probability event {L_e = 10}, which is measurable in s_{−e},
  P(s_e ≥ λ | s_{−e}) = 0.

So DH Theorem 6.1 cannot be applied to s. Neither can AH 9.10, which needs
arbitrarily high conditional raises (AH line 2485), nor AH 9.5–9.9 in their
stated form, since P0 resamples from P(·|ω_{F^c}). The packet correctly does
not claim these applications. My argument is stronger than the packet's
caution: the hypothesis is false, not merely unverified.

**(c) Exact-splice transfer.** Source04 relies on edge weights shared exactly
on a half-plane. Capping an iid splice changes cap weights in a random band
around the cut. A barrier argument (P) is therefore needed. It is not a
change of label.

**(d) Antecedent devices.** ADH Appendix C works only in the half-plane. Its
proof rests on the Wehr–Woo lowest bigeodesic γ0 = lim G((−n,0),(n,0))
(Proposition C.1), and upward finite energy of the field (Lemma C.2). It uses
open half-circuits only for the upper bound τ ≤ CDn^{3/2} in (26), not to
build a surrogate metric. Jacquet arXiv:2310.04091v1 uses penalized geodesics
for pattern counts and has no structural or Busemann content. Uniform iid
clipping preserves no bigeodesic set under any paid theorem.

**Conclusion.** The target needs a mechanism I would describe as "finite energy
by proxy". It works on the underlying coordinates (t,V) through a field that
has metric regularity but no finite energy. Circuit geometry makes the proxy
usable: monotone cap response to upward original moves, finite and tight cap
influence, walls that force long protecting circuits, and statuses that
preserve L. Bridges D, S and P carry this mechanism through DH Section 6, AH
Section 9 and source04. Each replaces an argument whose specific hypothesis
fails. This is not finite-union bookkeeping, and it is not a robust transfer
of a paid estimate.

**Counterweight.** An experienced FPP author would see "perturb the underlying
field" as the natural strategy. Taken alone, C1–C3, W, O, B and T are each
short or verbatim. That is why I call this lower-end SUBSTANTIAL. I credit no
operation merely for appearing in combination. Without D, S and P, the
classification would be BLOCKED rather than TECHNICAL, because no cheap route
reaches the full target.

## 4. Where the novelty sits

New: D, S, P and the short W. Nothing else is credited as new. In particular,
the following are not new: exact bigeodesic equivalence (classical circuit
surgery), cap moments and shape (A2 shape theorem), optional endpoint
corrections, same-status lowering, two-status tilt kernels, density and
posterior identities, the Abel bound, and the source05–08 contradiction.

## 5. Antecedent search and coverage

- **Primary bodies.** I re-read the operative primary passages listed in
  `reading-limits.md`, plus DH arXiv:1512.00804v2 Conjecture 1 and §1
  (retrieved by me).
- **Web.** Six bounded searches on 2026-10-18 (queries in
  `history-search.json`). They found no moment-free full-plane bigeodesic
  result, no Busemann or structural theory for iid laws without the
  Cox–Durrett moment, and no dependent-cap reduction. The only hit for
  "no bigeodesics … 2026" was the pinned OpenAI preprint itself.
- **Campaign.** Searching for bigeodesic, first-passage and No-bigeodesics in
  tracked non-private files outside campaigns found only catalogue snapshots.
  Inside campaigns, the only matches were r74 itself, its parent and Astra
  coauthor directories, and unrelated catalogue screens. There were no family
  212 hits in `accepted-retention-20261018/audit.json`. The strict-convexity
  companion's `consequences.tex` covers Gamma and exponential laws, which
  satisfy the minimum moment, and fixed directions. Its line 123 credits
  source212 itself.

These searches are bounded. They are not a semantic clearance and not a
worldwide priority certificate.

## 6. REQUIRED objections

1. **R1 (gate condition).** SUBSTANTIAL holds only if the independent proof
   gate validates D, S and P, and W including its diagonal parity and the
   selector premise S supplies. It must also validate the AH 6–8 and 10 proof
   reuse at the listed use-sites. The packet's AH maps are author integration,
   not verification. If D, S or P fails without repair, record BLOCKED. Do
   not downgrade to TECHNICAL, and do not narrow the target.
2. **R2 (eligibility record and paid class).** The acceptance record must say
   that source212 already pays every nonatomic G with
   E[min of four^2] < infinity, including unbounded and finite-mean laws, not
   only bounded G. The new class is exactly E[min of four^2] = infinity. The
   record must also say that the full target equals DH 1512.00804v2
   Conjecture 1 for finite-valued laws, and must not describe it as resolving
   that conjecture until every later gate passes. The packet's "Bounded G is
   source-paid" framing overstates the new class.
3. **R3 (locus of novelty and credit).** Any contribution statement or
   manuscript must locate novelty only in D, S, P and W (§4). It must cite
   classical circuit surgery (ADH C.5 and (26); Cox–Durrett/Kesten contours),
   and the A2 shape theorem (AH §3.1 and DH, through Boivin) as the paid route
   for cap shape. AH 9.10 Case 1 must be cited as the direct antecedent of the
   wall. The phrase "Parent author contributions are substantial" in
   `comparison-and-dependencies.md` is about coauthor attribution. It must not
   be read as, or carried into, a contribution claim.
4. **R4 (standing-hypothesis precision).** Candidate §5(a) says "Apply DH's
   averaging and pre-coalescence results under A2′" and includes DH 6.2 in
   that list. DH 6.2 and the triple extraction sit under Section 6's standing
   UFE hypothesis (DH line 1350). They are paid only as proof-level reuse
   (true at lines 1375–1470 as I read them). Every AH Sections 6–10 citation
   is likewise a proof-level reuse under a standing A1/A2 hypothesis that
   includes (v). The candidate must state this explicitly at each such
   citation, to avoid any appearance of applying a finite-energy theorem
   without its hypothesis.

## 7. Optional items

- O1. Add the explicit failure of upward finite energy (§3(b)) to the
  candidate. It justifies bridges D, S and W better than "not asserted".
- O2. Add the Kesten/Cox–Durrett necessity (§3(a)) as the reason the original
  metric cannot carry the structural input.
- O3. Mark the in-packet cap-shape proof as an optional self-contained
  alternative to the A2 shape theorem, or keep it and state that it is
  redundant.
- O4. The DH Lemma 6.4 bound c+ < λ+_0 is vacuous for the unbounded cap. Say
  so, so that a reader does not look for a cap analogue.
- O5. Keep the Jacquet clipping and linear-cap retention material labelled as
  history. They support non-routineness of the cap design but play no role in
  the proof.

## 8. Validation in this review

- Author identity: the external anchors match and `verify.py --anchor` passed.
  This is bytes only.
- My review packet is sealed by `manifest.json` and checked by `verify.py`
  (adapted from `agm063-contribution-r1/verify.py`, provenance in its
  docstring). Copied positive and reason-checked negative controls are
  recorded in `controls/`.
- No checksum, simulation or finite check is evidence of the theorem.
