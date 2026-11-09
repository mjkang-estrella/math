# Independent adversarial review: MathDB 338887 (Chan–Levine, Abelian networks IV, Conjecture 8.3)

Lane: `chanlevine-review-r1`. Reviewer: Claude Opus 5.5 (high effort). Date: 2026-11-03 (UTC).
This is a review, not an acceptance. Root decides. I used no child agents, did not run Lean, lake,
leanchecker or SAT solvers, ran one capped `python3 -I` process at a time, and wrote only in this lane.

**Overall recommendation: PROCEED_TO_LEAN**, with two conditions.

1. The Lean endpoint must be literal. It has to state the result in the source's network language
   (rotor dynamics on C_n, the legal relation, components, Definition 5.2 recurrence, r(C)), or root must
   explicitly rule otherwise. The uncompiled draft states only the count form, which is not enough under
   the campaign rules.
2. The uniqueness of C_{n,m,i} must be proved, not cited. The source only says "one can check" this, and
   the proof under review relies on it.

The mathematics of the candidate proof is correct. I found no error in any step.

| Gate | Verdict |
|---|---|
| A. Statement fidelity | PASS |
| B. Reduction to a count | QUALIFIED_PASS |
| C. Core argument | PASS |
| D. Prior art (bounded) | QUALIFIED_PASS: no resolution found |
| E. Significance and exclusion screen | QUALIFIED_PASS: genuine resolution, short and elementary |

Paths below are relative to `new-twenty-2026-10-31/`. Source line numbers refer to
`expanded-corpus-r127/sources/txt/1804.03322.txt` (v2) unless marked v1. Proof line numbers refer to
`expanded-corpus-r127/outputs/338887-proof.md`.

---

## 0. Input binding

- I hashed all 403 files under `expanded-corpus-r127/` before the review (`hashes/r127-before.sha256`) and
  after it (`hashes/r127-after.sha256`). The two lists are byte-identical. Both files have sha256
  `1cd9632ea48fed21fddf618f157290d402ef1dc8ce2a76d5b82fad25271228b4`.
- `raw/338887.jsonl` has sha256 `928ea2c6a9491df0f45641d529dcbdee9fd75c3959890becfbcf04ae39077bd2`. This
  equals the hash the brief gives for MathDB raw line `mathdb-normalized-chunk-0005.jsonl` line 3299.
- Proof `outputs/338887-proof.md` has sha256 `6fb4a080…122da05`. Lean plan `338887-lean-plan.md` has
  sha256 `3e8aa611…6122e`. Lean draft `formal/ChanLevine338887.lean` has sha256 `3b796dbc…22f`. Source
  text v2 has sha256 `76447ccd…53f5e`, and v1 has `541706e4…ed32f`.
- I did not run or import any r127 script. Everything under `scripts/` here was written fresh for this
  review.

---

## A. Statement fidelity: PASS

**Source text.**
- §8.3 starts at v2 line 4101 (v1 line 4051). It defines the edge weight as wt(v_k, v_{k−1}) = 1 and 0
  otherwise, and the configuration weight as wt(x.q) = Σ_k x(v_k)·k + wt(q(v_k)) mod n.
- Lines 4115–4119 say that executions preserve weight, and that "one can also check that, for any positive
  m and i ∈ Z_n, there exists a unique recurrent component that has total number of chips m and weight i".
  v1 says "level m" instead of "total number of chips m".
- Conjecture 8.3 is at v2 line 4127 (v1 line 4075). It reads: "For n ≥ 3, m ≥ 1 and i, j ∈ Z_n,
  r(C_{n,m,i}) = r(C_{n,m,j}) whenever gcd(n, m, i) = gcd(n, m, j)." The wording is identical in v1 and v2.

**The network.**
- Example 3.11 is at line 1035. When a chip at v is processed, the rotor first advances to the next edge
  and the chip then moves along the new rotor. On C_n, with two out-edges per vertex, the cyclic order is
  forced, so advancing simply flips the rotor.
- Recurrence is Definition 5.2 (line 2254), with its equivalent forms in Lemma 5.3 (line 2266).
- Components are classes of the legal relation (Definitions 4.6 and 4.7, lines 1533 and 1550). Recurrent
  components are Definition 4.8 (line 1637).
- r(C) is the number of recurrent configurations in C. Configurations are x.q with x ∈ Z^V: chips are
  labelled by vertex, and nothing is taken up to rotation.

**Level equals total chip count.** The MathDB statement and v1 say "level m", while v2 says "total number
of chips m". These agree for rotor networks:
- lvl(x.q) = cap(N) − cap(q) + sᵀx (line 2731);
- cap(N) = 0 and s = 1 for agent networks (Lemma 7.8(i), line 3842, and equation (7.1));
- 0 ≤ cap(q) ≤ cap(N) (Lemma 5.18(iii), line 2747), so cap(q) = 0;
- hence lvl(x.q) = Σ x.

**"Depends only on gcd" versus the equality form.** For fixed n and m, the equality form says exactly that
the map i ↦ r(C_{n,m,i}) is constant on the fibres of i ↦ gcd(n, m, i). That is the same as saying it
factors through the gcd, so the two forms are equivalent. gcd(n, m, i) is well defined for i ∈ Z_n
because n is one of its arguments, and gcd(n, m, 0) = gcd(n, m).

**MathDB 338887** (raw line, sha above) states the same thing with the same quantifiers, and with "the
unique recurrent component of level m and weight i". It does not repeat the definition of the weight; that
is an implicit reference to the source, not a fidelity defect. Proof lines 5–26 restate the source
correctly. One small slip: proof line 44 cites "§3.5" for irreducibility, but the statement is in §3.6,
lines 1029–1034.

---

## B. Reduction: QUALIFIED_PASS

The reduction (proof lines 40–64) uses these source results. Each is applied under its exact hypotheses.

- **Theorem 7.4, the cycle test (line 3685).** Its hypotheses are: a finite, locally irreducible, strongly
  connected agent network. The rotor network on C_n is an agent network (line 3579). C_n is strongly
  connected. All §3.6 networks are irreducible (line 1029), so every state is locally recurrent and (C2)
  holds automatically (line 1034). For rotor networks the rotor digraph is ρ_q = q, with edge set
  {q(v)} (line 3646). Theorem 1.3 (line 336) is the same statement, credited to Tóthmérész. Proof lines
  42–45 apply this correctly.
- **Directed cycles of q on C_n, n ≥ 3 (proof lines 47–53).** These are exactly the facing pairs plus the
  two Hamiltonian cycles. This is correct: in a functional digraph on a cycle, a walk that reverses
  direction closes a 2-cycle, and a walk that never reverses goes all the way round.
- **Lemma 5.19 (line 2792)** says a component is recurrent iff it contains a recurrent configuration. Its
  hypotheses (finite, locally irreducible, strongly connected, critical) hold, since agent networks are
  critical (line 3592).
- **Weight invariance** is a "one can check" remark in the source (line 4115). It is trivially true and I
  checked it directly. A chip moving v_k → v_{k−1} changes Σ k·x by −1, and its rotor changes from weight
  0 to weight 1. A chip moving v_k → v_{k+1} changes Σ k·x by +1, and its rotor changes from weight 1 to
  weight 0. Wrap-around moves are the same mod n. The total change is always 0 mod n.
- **Uniqueness of C_{n,m,i}** is also only a "one can check" remark in the source (line 4117). This is the
  qualification on gate B. Proof line 57 uses it without proof. It is true, and it follows rigorously from
  results the source does prove:
  - Proposition 7.9 (line 3881) gives |Rec(N, m)| = |Tor(N)| for m ≥ 1.
  - Theorem 5.25(i) (line 2936) gives Tor(N) ≅ Z^V_0 / (I − P)K. Here K = 2Z^V and P = A/2, so
    (I − P)K = (2I − A)Z^V = (D − A)Z^V. Tor(N) is therefore the sandpile group of C_n, which is Z_n and
    has order n. This is also Example 5.26 (line 2957): the Pham index gcd_v t(C_n, v) = n.
  - Every weight i ∈ {0, …, n−1} is attained by a recurrent configuration at every level m ≥ 1. For
    example, put all m chips at v_0, set q(v_k) = "−" for 1 ≤ k ≤ i and "+" otherwise. The only facing pair
    is (0, 1), which contains v_0, or q is constant with chips on its n-cycle; the weight is i.
  - Weight is constant on components, and there are exactly n components and n weights. So there is
    exactly one component of each weight.

  This derivation is absent from the candidate. It should be added to the paper and is needed in Lean.
- **Exactness of the count.** Recurrent configurations in the same component are mutually reachable,
  because Definition 5.2(ii) applies in both directions. So r(C_{n,m,i}) is exactly the number of
  recurrent configurations with Σx = m and weight i. Nothing is over- or under-counted. Classes and
  configurations are not confused. Chips are vertex-labelled. Rotor states are counted exactly once each,
  because on a simple digraph the state is determined by the rotor digraph (line 3647). The encoding
  wt = Σ k·x(k) + #{k : q(k) = −} (proof line 61) matches the source's weight.

**Independent confirmation from the definitions** (`scripts/brute_def.py`). Tier 1 builds the full
trajectory digraph on {x ≥ L, Σx = m} × Q. That set is finite and closed under legal moves. On it,
Definition 5.2 holds exactly when x.q lies in a terminal SCC; the script docstring gives the proof. For
every n ≤ 7 with m ≤ 2n, and for n = 8 with m ≤ 11:
- there are exactly n terminal SCCs;
- each has constant weight, and the weights are pairwise distinct;
- there are no non-terminal cycles.

That is, uniqueness holds and r(C) is the SCC size. With L = −1 (negative entries allowed; n ≤ 5 with
m ≤ 2n, and n = 6 with m ≤ 10) the terminal SCCs and counts are unchanged and contain no negative entry.
This is consistent with condition (C1). Logs: `logs/def-L0-*.log`, `logs/def-Lm1.log`.

---

## C. Core argument: PASS

I checked every step by hand.

- **Step 0, Fourier inversion (line 71).** Standard; correct.
- **Step 1, rotation (lines 73–75).** wt∘ρ = wt + m, including the wrap term (n·x(n−1) ≡ 0). The cycle
  conditions are invariant under rotation. So W_m(ω)(1 − ω^m) = 0. Correct.
- **Step 2, inclusion–exclusion (lines 77–95).**
  - R′ ∖ R consists of exactly the two configurations with x = 0 and q constant. If x = 0 and q is not
    constant, q has a facing pair that contains no chip. Both extra configurations have weight ≡ 0.
  - Facing pairs are disjoint for fixed q.
  - The display at line 87 shows only the x-part of the generating function. The factor ζ^{#minus(q)} is
    supplied correctly in the next sentence: the edges of M contribute ζ^{|M|}, and each free vertex
    contributes 1 + ζ.
  - So G′ = Σ_M (−ζ)^{|M|} Π_{k∉V(M)} (1 + ζ) f_k. Correct.

  I also checked by hand that this equals the source's Theorem 7.11 determinant with y on (v_k, v_{k−1})
  set to ζ, y on (v_k, v_{k+1}) set to 1, and z_{v_k} set to tζ^k. Expanding the cyclic tridiagonal
  determinant gives the matching terms, and the two n-cycle permutations give exactly −2D(t). So
  G = det(D_G(y, z) − A_G(y)), as line 95 says.
- **Step 3, transfer matrices (lines 97–107).** X_k[2,2] = 0 forces every step 1→2 to be followed by a
  step 2→1. This gives a bijection between closed state sequences and matchings of the n-cycle, including
  the wrap domino {n−1, 0}. The weights are (−ζ g_k)·g_{k+1} for a domino and 1 + ζ for a singleton.
  Correct.
- **Step 4, periodicity (lines 109–112).** The product equals P^{n/e}. Π_{k<e}(1 − tζ^k) = 1 − t^e.
  det X_k = ζ g_k². det P = (1 − t^e)². The Cayley–Hamilton recurrence for V_j follows. Correct.
- **Step 5, the trace identity (lines 114–125).**
  - Rotation: X_k(ζt) = X_{k+1}(t), so by cyclicity p(ζt) = p(t), and p_j = 0 for 0 < j < e.
  - Constant term: the characteristic polynomial of A is (λ − 1)(λ − ζ), so p_0 = 1 + ζ^e = 2. This also
    holds for e = 1.
  - Top term: the t-coefficient of X_k is ζ^k·J, and J² = −ζI.
  - For e odd, Tr J^e = 0.
  - For e even, ζ^{e/2} = −1 and ζ^{e(e−1)/2} = −1, so p_e = −2(−ζ)^{e/2} = 2(−1)^{e/2}.
  - So q_e = 0, 2 or −2 as claimed. Correct.
- **Step 6, conclusion (lines 127–135).** V_r ∈ Z[t^e] depends only on (e, r), so W_m(ζ) = w_{n,m}(e) ∈ Z
  depends only on the order e of ζ, and it vanishes unless e | m. The Ramanujan sum c_e(i) depends only on
  gcd(e, i). For e | d we have gcd(e, i) = gcd(e, gcd(d, i)). Correct.

**Attempts to break the argument.**
- Small n, n = 3 in particular: the cycle graph is still simple and the wrap domino is handled.
- e = 1 and e = 2.
- e = n with r = 1.
- m not divisible by e.
- i = 0.
- Rows where gcd(n, m, i) differs but the counts happen to coincide. Example: n = 6, m = 12 gives
  [58810, 58800, 58800, 58810, 58800, 58800]. The values for gcd 1 and gcd 2 coincide there. That is
  allowed: the conjecture only claims equality when the gcds are equal.

None of these broke anything.

**My own computations.** All exact arithmetic; all scripts new.
1. **Brute force from the definition, two independent tiers.**
   - Tier 1 is the Definition 5.2 terminal-SCC method described under gate B.
   - Tier 2 (`scripts/brute_greedy.py`) uses forward dynamics through Lemma 5.3(iii): a legal execution
     with |w| = r = (2, …, 2). It finds one greedily; the removal lemma (Lemma 4.2, line 1435) shows the
     greedy search is exact.
   - Tier 2 caps chips at 2 per vertex. I checked that the capped and uncapped versions agree on every
     configuration for n ≤ 6 and m ≤ 2n: 1,292,664 configurations, 0 mismatches.
   - Coverage: tier 2 covers n ≤ 8 with m ≤ 2n, plus n = 9 with m ≤ 18.
   - Result: tiers 1 and 2 agree on all 66 overlapping (n, m) cases.
2. **Conjecture and closed formula** (`scripts/compare.py`).
   - Conjecture 8.3 holds in all 66 + 18 cases.
   - I re-implemented the closed formula from the text of proof lines 28–38: Lucas sequence,
     coefficient extraction and Ramanujan sums. It equals the brute-force counts exactly in all 84 cases,
     always as an integer.
   - For every e | n, I computed W_m(ζ) = Σ_i N(i)·ζ^i exactly modulo Φ_e. In every case it is a rational
     integer, it is 0 when e ∤ m, and it equals w_{n,m}(e). This checks Steps 1 and 6 directly, not just
     the final formula.
3. **Trace identity, symbolically** (`scripts/trace_sym.py`). Working in Z[z]/Φ_e[t], which covers all
   primitive e-th roots at once, for every e ≤ 16 as required, and again up to e ≤ 40, all of these hold:
   - Tr(X_0⋯X_{e−1}) = 2 + q_e·t^e;
   - det P = (1 − t^e)²;
   - Π_{k<e}(1 − tζ^k) = 1 − t^e;
   - the t-coefficient of X_k is ζ^k·J, and J² = −ζI.
4. **Table 8.1 of the source** (lines 4134–4148). All six rows, n = 3 to 8, are reproduced entry for
   entry by both tiers. For example, row 8 is 130090, 130080, 130072, 130080, 130086, 130080, 130072,
   130080.

---

## D. Prior art: QUALIFIED_PASS (no resolution found; bounded search)

All searches ran on 2026-11-03. Receipts are under `fetch/*/receipt.json`.

- **OpenAlex** (only allowed index; I did not supply an email or API key, and ignored the API notice
  that invited agents to request a key with the user's email):
  - The Memoir is W2797617178 (DOI 10.1090/memo/1358, 2022), with 4 citing works:
    - Chan, "Rotor walks on transient graphs…" (2019);
    - Chan, "Recurrence of horizontal–vertical walks" (2023);
    - Kiss–Levine–Tóthmérész, "The devil's staircase…" (2024);
    - Greco–Levine, "Branching in a Markovian environment" (2021).

    None concerns cycle component counts.
  - A title search also found Kaiser–Klötzer–Huss (2026, stochastic networks), which is not relevant.
  - Chan's works (A5001503583, 2021–2026) are on posets, correlation inequalities and the
    Alexandrov–Fenchel inequality, with no rotor work.
  - Levine's works since 2019 (A5052050258) include no rotor-on-cycle counting.
  - Topic searches ("sinkless rotor network recurrent configurations", "rotor configurations cycle
    recurrent component weight gcd", "chip-and-rotor configurations cycle graph enumeration") return
    only the source and classical rotor or sandpile papers. These include Pham (2015) on rotor-router
    orbits, Huss–Sava-Huss, Poghosyan–Priezzhev on unicycles, and Auger–Coucheney–Etse (2026) on
    reachability. None gives the weight-refined count.
- **Chan's 2019 Cornell thesis** ("Nonhalting abelian networks"; r127 cached copy, read only). It has no
  §8.3 material: grep finds no weight function on C_n, no gcd(n, m, i), no Table 8.1 values, and no
  concluding conjecture.
- **AMS.** www.ams.org/books/memo/1358 redirects (301) to pubs.ams.org/ebooks/memo/1358, which is open
  (HTTP 200). It serves the abstract only; there is no erratum or resolution note. I had no full-text
  access to the published Memoir, so I cannot rule out a wording change in the published §8.3. arXiv v1
  and v2 agree.
- **Not checked** because the routes are denied or out of scope: Crossref, Semantic Scholar, the arXiv
  search API, Google Scholar citation lists. OpenAlex's citation coverage looks sparse, since 4 citers is
  low for a Memoir.
- **Classical literature and "routine consequence" check.**
  - The total count Σ_i r(C_{n,m,i}) follows from the source's Theorem 1.4 and 7.10.
  - The weighted generating function is the source's own Theorem 7.11 master determinant, evaluated at the
    substitution given under gate C, Step 2.
  - Evaluating a cyclic tridiagonal determinant as "trace of the transfer-matrix product minus the two
    cyclic terms" is classical.
  - Those are known ingredients. What is not in the source, and what I could not find elsewhere, is the
    specialisation to roots of unity combined with the period-trace identity Tr P = 2 + q_e t^e. That
    identity is what makes W_m(ζ) depend only on ord ζ.
  - Known sandpile and rotor results on cycles give the number of components (n, the Pham index) but not
    their sizes by weight.

---

## E. Significance and exclusion screen: QUALIFIED_PASS

- **Not a known result.** I found no public proof. The source's authors had Theorem 7.11 in hand and
  still wrote that "the general case seems more mysterious" (line 4131). The equality form is a published
  conjecture in an AMS Memoir.
- **Not a wording artefact.** The statement is the literal conjecture with all its quantifiers.
- **A full resolution.** The proof covers every n ≥ 3, m ≥ 1 and i, j, and it gives an exact closed
  formula in addition.
- **Risk.** The proof is short, about one page, and elementary. Each tool is standard: inclusion–exclusion,
  transfer matrices, Cayley–Hamilton and Ramanujan sums. The bridge to the network uses the source's own
  theorems. I do not think it is a routine corollary: the key trace identity is a genuinely new
  observation, and without it the source's determinant does not reveal the gcd dependence. But root
  should weigh the brevity against the substantive-credit standard. In my judgement it is eligible.

**Lean plan** (uncompiled; reviewed by reading only).
- `chan_levine_conjecture_8_3` is a count-form theorem about `recCount`. It is not literal. The file says
  so itself (`ChanLevine338887.lean` lines 8–12; `338887-lean-plan.md` lines 19–22).
- The definitions `Recurrent`, `weight` and `recCount` (lines 29–46) correctly encode the cycle test on
  C_n for n ≥ 3 and the source's weight.
- The `orbit` lemma statement (lines 102–104) is true. Lift a unit mod d to a unit mod n; then the
  difference j − u·i lies in dZ_n = mZ_n.
- `w` (lines 76–81) matches the formula.
- Under the campaign rule (kernel-checked theorem for the exact MathDB statement, with all bridges), a
  literal endpoint is needed, and one is feasible because the network is concrete. The required bridges
  are:
  - **L1, dynamics.** Define the rotor dynamics on C_n with the advance-then-move rule, legal executions,
    the legal relation, components, Definition 5.2 recurrence and r(C). Prove chip and weight invariance.
    This is easy.
  - **L2, the cycle test on C_n.** Definition 5.2 recurrence ⇔ `Recurrent`. This is moderate work. A direct
    C_n proof is possible: show that recurrence means returning to itself through a word with |w| = 2·1,
    then handle facing pairs and Hamiltonian cycles. Alternatively, formalise Lemmas 5.3, 5.5, 7.6 and 7.7.
  - **L3, uniqueness.** All recurrent configurations with level m and weight i form one component. This is
    the hardest bridge. The source route goes through Tor(N) ≅ sandpile group (Theorem 5.25, Proposition
    7.9), which is heavy to formalise. A direct C_n argument is probably cheaper, but I did not construct
    one: route all chips to v_0 using v_0 as a sink, then connect the resulting canonical configurations of
    equal weight.
  - **L4.** r(C_{n,m,i}) = `recCount n m i`, which follows from L2 and L3.
  - The analytic core, `W_primitive` and the DFT step, is as the plan describes. It is substantial (the
    plan estimates 600–1200 lines) but routine to formalise.
- Root should also note that a literal statement must either assert uniqueness as part of the theorem, or
  quantify over every recurrent component of level m and weight i. Either way L3 is needed, because
  without it r(C) is only a part of N(i).

---

## Process record

| Run | Script | CPU (s) | Max RSS (KB) | Result |
|---|---|---|---|---|
| def-L0-small | brute_def.py, n = 3 to 5 | 0.3 | 16 052 | uniqueness true; Table 8.1 rows 3 to 5 match |
| def-L0-n6 | brute_def.py, n = 6, m ≤ 12 | 5.2 | 63 484 | ok |
| def-L0-n7a, def-L0-n7b | brute_def.py, n = 7, m ≤ 14 | 21.1, 77.4 | 656 720 (peak) | ok |
| def-L0-n8a, def-L0-n8b, def-L0-n8c | brute_def.py, n = 8, m ≤ 11 | 32.9, 34.4, 67.3 | 1 057 484 (peak) | ok; Table 8.1 row 8 matches |
| def-Lm1 | brute_def.py with L = −1 | 16.8 | 289 728 | ok; no negative entries in recurrent configurations |
| greedy-n3 to greedy-n9 | brute_greedy.py | at most 32.7 | 54 756 (peak) | literal versus capped check: 0 mismatches |
| trace-sym-16, trace-sym-40 | trace_sym.py | 0.06, 3.3 | 12 596 | all_ok true |
| compare-n3-8 | compare.py | 0.02 | 11 952 | all_ok true (66 cases) |
| compare-n9 | compare.py | small | small | 0 mismatches in 18 cases (all_ok is false only because Table 8.1 has no n = 9 row) |

**Candid notes.**
- The first `compare-n3-8` run had a bug in my own script. I used ζ^{i·n/e} where ζ^i was correct, which
  produced spurious W mismatches. I fixed it and reran, and the rerun overwrote that log.
  `logs/compare-n3-8.*` is the corrected run.
- Every process ran through `scripts/run.sh`: taskset to 2 CPUs, `ulimit -t 120`, `ulimit -v` 6 GiB,
  timeout 140 s, `MALLOC_ARENA_MAX=2`, `python3 -I`, strictly sequential.
- Network calls were made with `scripts/fetch.sh`: one `curl` per URL, each into its own fresh empty
  directory, with no retries. No 403 or 429 responses occurred.
- No background job was left running from this lane.
- File hashes for this lane are in `hashes/lane-manifest.sha256`.
