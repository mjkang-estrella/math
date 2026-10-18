# RCS128 independent proof review, round 1

Reviewer: fresh independent proof-review sub-agent (Claude Opus 5.5), assigned directory `frontier/campaigns/2026-10-14/rcs128-proof-r1/` only. I am not an author. I made no edits to author files or shared ledgers, and I did no staging, committing, uploading or publication. I started no nested agents. Original prose CC BY 4.0; original reviewer code MIT.

## Verdict

**PASS_FULL_RCS128**, at the level of a full adversarial mathematical proof review, for the unchanged original scope.

I re-derived every new step and quantifier of `candidate.md` against the stipulated source operations (sections 02–07, read in full). I found **no gap, false statement or counterexample**, and there are **no required repairs**. The optional findings below are clarity and presentation points. None of them changes the algorithm or the bound.

What this verdict is not:

* It is not acceptance, a count increment, a contribution or novelty verdict, a manuscript PASS, Lean or full formalization, or publication. Those gates belong to the parent.
* My finite diagnostics, including a reviewer-written end-to-end executable model, are supporting evidence only. They are not the basis of the verdict and are not "full algorithm execution on all inputs".

## Identity and integrity checks performed

* Frozen packet `frontier/campaigns/2026-10-14/fresh-structural-discovery-r37/`. I recomputed SHA256 for the four externally anchored files and all four match the handoff: MANIFEST `a81ea233…bb96a6`, candidate `ebfed67a…39137`, scope `7dfa38db…bf0`, checkpoint `3ab70804…bf0`.
* I inspected `verify.py`, `checks.py`, `check-new-interfaces.py`, `explore.py` and `search-budget.py` before running them. They contain no writes except the `--write` branch under `__main__` in `check-new-interfaces.py`, which the replay does not reach. `runpy` uses a non-`__main__` run name.
* `python3 -B verify.py --expected-manifest-sha256 a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6 --replay` returned PASS: 51 payloads, 13 pinned sources, 1 primary, 4 contexts, replay true. An all-zero anchor failed with `external manifest anchor mismatch`, exit code 1.
* I independently compared the 13 source bodies with the repository's own `sources/preprints-tree.json`, which is nontruncated with 13223 entries, at pinned commit `fd4aeeb2…eeb`. All 13 Git blob SHA-1 values match, and the packet's tree copy is byte-identical to the repository file.

## Scope check

The candidate's statement (§Statement) matches `original-scope.txt` exactly. It covers:

* every explicitly encoded finite alphabet and involution;
* every finite explicit family, including fixed letters, palindromes, duplicates, substring redundancy, empty words and the empty family;
* deterministic polynomial bit complexity in the total encoded input;
* output containing s or rho(s) for every input, with length ≤ 2·OPT_RC.

There is no fixed alphabet, no bounded length, no nonpalindromic restriction and no promised period. I reviewed this original scope. No narrowing was used anywhere in my review.

## Step-by-step re-derivation

Notation follows the candidate. "Source" means the pinned manuscript sections.

### S1. Preprocessing (§1)

Dropping empty words and dropping orbits contained in a different orbit preserves feasibility and OPT_RC. If s ⊂ t, then rho(s) ⊂ rho(t), so either orientation of t covers one orientation of s.

Equal-length containment is equality, so every surviving required word is maximal in V. V is closed under rho and under substrings. The empty and all-empty cases output the empty word, which is optimal. **Verified.**

### S2. Count lemma with the self-text surplus 2k+1 (§1)

Let A be self-reversed, with cm(A(j)) = A(c−1−j). Then rho(A[x:e)) = A[c−e : c−x).

For v = A[0:h), rho(v) occupies A[c−h, c). The A-aligned starts of w (starts ≡ 0 mod p) inside it run over an interval of kp+1 consecutive integers. That interval contains k or k+1 such starts, so at least k. **Verified.** The note's phrase "last start at most kp−1" is loose; see O8.

**Case N(v) > B_A(v;N).** Take an unblocked occurrence of v in one tagged component.

* Its k+1 internal copies of w share the same global A-alignment, so each has the same nearest-mismatch bracket as v. Hence they are unblocked.
* In the other component, the reflected occurrence of rho(v) contains at least k copies of w with one common A-alignment. Their bracket is the bracket of rho(v).
* Reflecting such a bracket gives a bracket of the original v. Both mismatch letters map to mismatches because cm is a bijection: cm(r(|r|−1)) ≠ cm(A(·)) = A(c−1−·). The reflected word lies in V because V is rho-closed.
* Therefore a blocked reflected copy would block v, which contradicts the choice of v.
* The tagged components make the 2k+1 occurrences distinct.

**Verified.**

**Case N(v) = B_A(v;N) > B_A(v;m).** I re-derived the reflected bracket explicitly.

* If r has interior r(h) = A(h−j), then rho(r)(h') = A(h' − j') with j' = |r| − j − c.
* The end mismatches map to end mismatches.
* The placements J ≡ j' (mod p) with J ∈ [|r|−j−h, |r|−j−|w|] satisfy 1 ≤ J and J + |w| ≤ |r| − 1. There are at least k of them, and each spells w.

So b_{A,w}(rho r) ≥ k. Because m and N are rho-symmetric, Δ(rho r) = Δ(r).

* Nonfixed r gives a contribution of at least (k+1) + k.
* Fixed r gives Δ(r) ≥ 2, even, because both m and N are even at fixed words. This gives at least 2(k+1). Reflected placements are not counted twice.

**Verified.**

**Remaining parts.** These are also verified:

* extension rules;
* required bounds (N(s) ≥ 1, and ≥ 2 for fixed s);
* orbit maxima and even rounding, since N is symmetric and even at fixed words;
* W = Σ_a m(a) ≤ Σ_a N(a) = 2|T|;
* m ≤ 2L;
* the descending order: every bound for a word of length ℓ refers only to longer words.

The nonleast-period case is also covered: self-reversedness is a property of the text, and the argument above uses only p-periodicity.

### S3. Base graph, τ, parity (§2)

* u(s) = d(rho s), because rho(cs) = rho(s)cm(c).
* τ maps the up edge pref(s)→s to the down edge rho(s)→suf(rho s) = rho(pref s). It reverses edges and has no fixed edge (up ≠ down).
* At a fixed nonempty s, the outdegree is m(s) − Σ m(csd). The words csd pair under rho, and fixed ones have even counts, so the outdegree is even.
* At ε the outdegree is Σ_a u(a) = Σ_{|s|=1} m − Σ_{|s|=2} m, which is even for the same reason.
* Adding C + τ(C) adds 2·outdeg_C at each fixed vertex.

**Verified.**

### S4. τ-paired walk decomposition (§2)

At a nonfixed vertex, the forced partner transition (τ e_out, τ e_in) is consistent. At a fixed vertex, the incoming copies are exactly τ(outgoing copies), and σ has no fixed point.

Suppose a cycle equals its τ-image. Then τ acts on its edges by i ↦ s−i on Z/n.

* If this map has a fixed point, that point is a fixed edge.
* Otherwise (n even, s odd), some consecutive pair is swapped, which gives a fixed transition.

Both are excluded. **Verified.**

### S5. Self-group reflection, profile fixation, phase parity, adjacent pairing (§2)

* R(x,e) = (c−e, c−x) is the reflection in the line x+e = c. It preserves window length and the NW direction (−1,+1), so it maps upper regions to upper regions and preserves the pointwise order of staircases.
* The group's phase-labelled edge multiset is R-invariant, because it is a union of walk pairs C, τC.
* Sorted profiles are the order statistics of the exit multisets. So R(sorted family) is an ordered family with the same exit multisets, and each profile is individually R-fixed.

Phase parity:

* For 2t+l ≡ c (mod p), the number of layers with z_i(t) ≥ t+l equals the number of original passages that record the phase-t occurrence.
* Recordedness is preserved by R (window containment is preserved).
* C ≠ τC, so these passages pair, and the count is even.

Adjacent pairing:

* At every phase threshold, an even tail containing the top member contains the next member. The lower member also has f ≤ the upper member's f, so it actually visits the vertex.
* The top two indicators agree at every threshold. Removing them preserves all even tails, so induction applies.
* x+e runs through 2p consecutive integers per turn. This gives exactly two axis windows per turn, and the lower member visits both.
* p = 1 is a degenerate but consistent case: every window is an axis window, and each turn has exactly two windows (O6).
* An ε crossing forces f = x for both members.

**Verified.**

### S6. Splice E, F (§2, §4)

* E is D1[U,V] followed by D2[V,U+(p,p)]. It is a monotone period-p staircase with p up steps, and E + F = D1 + D2.
* R fixes each axis vertex for the reflection centred on it, and swaps the two half-period arcs. So R(E) = F as window and phase-edge sets.
* Every window of D1 ∪ D2 lies on E or F, and its reflection lies on the other.

**Verified.** At copy level, see O2. Only vertex connectivity is used later.

### S7. Source operations in the forms used (§3)

* The band lemma and the ordered-windows lemma are verbatim.
* The geometric collective proof never uses the number of layers. It uses only the three inequalities and that K is a multiple of p, so it applies to an odd core of 2k−1 layers with K = kp.
* For the individual cases, the contact length is max(0, b−a−p) ≤ q.
* The host lemma's proof uses only that the host is a monotone period-q walk in the host text with ordered record windows, plus the host budget q. A spliced E qualifies.

**Verified.**

### S8. Recipient processing: anchor, flip, reclassification, baseline (§4)

**Single-record and anchor conditions.**

* Each child orbit uses one record. Its mirror batch is the τ-image.
* Naming E so that the anchor's original record lies on E keeps a genuine case-3 batch, so the host lemma's nonempty hypothesis holds.
* Flipped batches use the mirror copies, whose record lies on E.
* Distinct child orbits give distinct texts, all of period less than q.

**Reclassification.** Take the original window [a,e) with a+p < e ≤ b−p.

* It reflects to [c−e, c−a) at R' = [c−b, c−a). This window is right-anchored and starts at least p after a'.
* Since z is nondecreasing, f(a') ≤ f(u) ≤ b'.
* The three source cases then apply. Case 3 is exactly the left-anchored condition. Case 2 is a source individual link at R'. It touches R' on E, so it attaches once E is rooted, which happens inside the host lemma itself. It therefore creates no dependency on cycles.
* Case 1 is vacuous, because reflection preserves vertex lengths (O3).

**Costs.**

* The host lemma on E costs q, and its mirror on F costs q.
* Each requester pair pays 2p_i: either a loop and its mirror, or, for the least-period child j, a contact root of length less than p_j and its mirror.
* A self child requests through its upper member, whose profile is R-fixed. Its mirror request lies on the same profile, and the pair meets at the axes.

**Baseline.**

* The anchor record has length less than p_child + q < 2q.
* Every lower pair lies below whichever recipient member contains S, so the source lower-link inequalities hold. In nonself orbits the lower link must use the same-group member (O4).
* The upper member of the highest recipient pair gives the band and hard-case bound for the upper region.

**Verified.**

### S9. Upper processing (§5)

**Nonself orbits.** This is the source procedure on the canonical group, mirrored. Only canonical-group layers can carry the identical alignment, so the k+1 rule suffices. A record in the rho(A) group has period p and length less than p by the equal-period agreement bound. **Verified.**

**Self orbits, easy branches.** The root excursion through [t,H) touches every upper layer, and the cost is ≤ rp, plus its mirror. The band uses the baseline upper member with h = rp.

**Self orbits, hard case.**

* The threshold stops by k ≤ r, because baseline-or-lower layers satisfy l ≤ l_base(t) < H−rp.
* At the previous failed threshold there were at least 2k−1 qualifiers. This gives the core sharp band, and the translation argument gives the wide band ≤ kp.
* v = [t,H) is the top layer's own-text vertex and is unblocked, so the 2k+1 rule applies at the shifted text.
* At most 2k layers record w at the identical alignment, because each primitive layer has one such residue. A different alignment, which may be another phase of A, gives a record with a ≤ t, b ≥ H−K and |R| < p+q, with |R| < p when the period is equal.
* The collective inequalities for the core follow: r_H − r_L ≤ K and r_H ≤ H ≤ b+K.
* The 2k-th layer meets core layer 2k−1 at the shared axis vertices.
* The remaining individual pairs have f_upper(a) ≤ b in both branches.
* Requests satisfy b−a > 2p and b−a < p+q, so q > p.
* Every budget is used as whole pairs.

**Verified.**

### S10. Quotient cycles (§6)

* Targets: D and R(D) lie in one unit, or are both rooted (nonself: same rank in the partner group; self: R-fixed profile). So the functional graph is well defined.
* A selfloop has equal period and a distinct aligned text (including rho(A)), so |R| < p. Internal joining (2(k−1)p) plus 2|R| < 2p stays within the unit budget, and both ports are touched.
* For cycles of length at least 2, use the canonical lexmax over both orientations. Every rotation of either target orientation is ≤ the selected source's distinguished word. The max-rotation lemma then gives b−t < q, and x = min(t, a+K) gives b−x < q.
* All core first ends at x lie in (b, H], so the list [a,b), [x,b), [x,F), [a+K,b+K) is ordered with cost K.
* Omitting the target's pair frees 2q, which pays both contacts.
* The path minus the omitted edge ends at the target. Both target ports, D's port and R(D)'s port, touch rooted contact pieces. Rootedness then propagates backwards along the planned links to all other ports, whether the lift is twisted or untwisted.
* Distinct cycles are disjoint.

**Verified.**

### S11. Half-Euler (§7)

* The signed incidence at a nonfixed orbit is well defined. Quotient loops cannot occur in the hierarchical graph because |rho v| = |v| (O11).
* The number of + incidences equals outdeg and the number of − incidences equals indeg, which are equal. At a fixed vertex the quotient degree equals outdeg, which is even.
* Pairing opposite signs gives a trail whose directed lift is state-consistent: arriving through a + incidence puts the walk at rho(v), which then requires leaving through −.
* Cross-switching merges trails at a nonfixed vertex after aligning signs, and arbitrarily at a fixed vertex.
* The lift from the fixed root ε closes. It uses U edges, U/2 of them up, and visits a representative of every used orbit.
* The source suffix invariant then gives an output containing s or rho(s), of length U/2 ≤ W ≤ 2·OPT_RC.

**Verified.**

### S12. Complexity and degenerate inputs (§7)

* |V| = O(L²), counts ≤ 2L, and there are O(L⁴) rules, each evaluated in polynomial time.
* The self-reversal test is a rotation test.
* Edge totals: 2W ≤ 4L, and the final graph has 2U ≤ 8L.
* Comparisons of periodic texts need at most p+q letters, and labels are charged by bit length.
* Unused alphabet symbols are ignored after reading. The empty family, all-empty input, single fixed letters, palindromes and duplicates go through S1–S11 unchanged.

My model ran instances such as ['a'] with identity cm and ['ab'] with a↔b, where 'ab' is a palindrome under rho. **Verified.**

## Findings

**Required: none.** I found no missing step, false inequality or budget overlap.

**Optional** (clarity only; none affects correctness):

1. **O1.** Fix the comma splice in the §1 definition of g. This is the known prose typo.
2. **O2.** In §2 and §4, "τ(E) = F" holds for windows and phase-labelled edges. A copy-level identity would need a labelled assignment of base copies to sorted layers, and that is never used: rootedness is vertex connectivity, and mirrored constructions are new copies. Say this explicitly.
3. **O3.** Reclassification case 1 is vacuous, because reflection preserves vertex lengths and the original requester was in source case (iii).
4. **O4.** For nonself recipient orbits, S may lie on R(D). The lower link must then be built in the partner group with the same-rank member and reflected. The phrase "whichever member contains it" implies this; state it.
5. **O5.** In §5 for self groups, state that when the collective test fails, "remaining pairs" means all upper pairs, including the top k.
6. **O6.** For p = 1 in a self group, every window is an axis window. The "two axis vertices per turn" statement still holds because each turn has 2p = 2 windows. Mention this degenerate case.
7. **O7.** Individual-link contacts have length ≤ q, not < q. The cycle budget 2q covers this, as stated. Ties in the canonical-text selection, between units of one orbit, may be broken arbitrarily.
8. **O8.** Replace "last start at most kp−1" with the count of A-aligned starts in an interval of kp+1 integers, which is at least k.
9. **O9.** The least-period child j in the host lemma is chosen among children with surviving case-3 requests. Its contact root is paid by one such requester pair, which the excursion touches directly.
10. **O10.** Fix a deterministic tie order among orbits with equal least period. Correctness does not depend on it.
11. **O11.** The half-Euler lemma treats quotient loops in general, but in the hierarchical graph there are none.

## Finite diagnostics (supporting only; not proof)

All scripts were written independently by me in this directory. Commands, seeds and expected outputs are in `replay-expected.json`, and `verify.py --replay` reruns them with PYTHONHASHSEED=0.

* **Count recursion.** `rc_counts.py` implements the §1 recursion from the candidate text. A differential test against the author's frozen `compute` agreed on every instance tried (1500 + 800 + 2000 + 300 instances across seeds). Old rule on the W6/OPT7 instance gives W = 6; the broad rule gives W = 12.
* **Necessary condition W ≥ OPT_RC.** The output has length ≤ W and every feasible output has length ≥ OPT_RC, so W < OPT_RC would refute the theorem. The search covered:
  * exhaustively, all singletons, pairs and triples up to bounds (12, 7, 4) over four involutions: 297,492 families;
  * a random biased search: 60,300 instances.

  It found no W < OPT_RC. Count domination against N_T + N_rho(T) at the exact optimum T held on every random instance.
* **End-to-end executable model.** `rc_algorithm.py` implements counts, τ-paired transitions, lifts, sorted layers, pairing and both axes, splices, orbit processing, anchor/flip/reclassify hosts with the source host lemma, the odd core, quotient cycles, internal joins, and half-Euler extraction.
  * Every inequality the candidate asserts is an assertion in the model, and every budget is charged to disjoint pair or unit accounts.
  * The final graph is checked to be balanced, parity-correct, connected to ε, with up cost ≤ 2W. The output is checked to contain s or rho(s) for every input, with length ≤ W.
  * There was no assertion failure on any run.
  * Coverage over the recorded runs includes thousands of shared-axis pair checks, hundreds of odd-core units and host applications, quotient cycles and selfloops, and shadow checks of the reflected-batch reclassification lemma on every request (mirrors reclassified and the host lemma dry-run on the mirrored path).
  * Recorded totals (`host_cov_2[1-4].json`, 4×25,000 mutation rounds, earlier model version without shadow checks; `host_cov_11b.json` and the replay use the final version): ~35,400 host applications, 39 spliced self-recipient hosts, ~66,000 shared-axis pair checks, ~6,900 odd-core units, 3 failed-collective self branches, 218 quotient cycles of length ≥ 2 and 629 quotient selfloops.
  * **Actual multi-child flipped batches (`reclass2`/`reclass3`) occurred zero times.** The flip branch therefore rests on the hand re-derivation in S8, plus the per-request shadow checks of the reflected reclassification and of the dry-run host lemma on the mirrored host path. The shadow checks returned case 3 for all 386 shadowed requests.

  This is bounded execution of my model, not a proof and not a guarantee for all inputs.

## Reading limits

See `checkpoint.md` in this directory.
