# Independent adversarial review: exact slow NIM

Recommendation: **HOLD**. The mathematics survives independent review, and warrants a small literal Lean formalization once the source/prior-art gaps below are resolved. This is not acceptance. Root alone decides credit. Prefer MathDB **360653**, with **361128** linked as a duplicate, at most one credit.

Gate verdicts: **A QUALIFIED_PASS; B PASS; C QUALIFIED_PASS; D QUALIFIED_PASS; E QUALIFIED_PASS.** Qualifications are evidence limitations or required packaging corrections, not mathematical counterarguments. No Lean process was run, and no kernel certificate is claimed.

## Scope and evidence binding

Review date: 2026-11-05 UTC. All writes, caches, temporary files, downloads, and logs are inside this lane. No child agents, git commands, browser tabs, messages, or uploads were used. Discovery programs were read but never imported or executed. `scripts/check.py` is an independent implementation. `scripts/run.sh` applies a 6 GiB process-group RSS watchdog, CPUs 0 and 1, CPU 120 s, wall 140 s, and MALLOC_ARENA_MAX=2. Python was invoked with `-I` and an absolute script path. Each HTTP attempt has its own fresh directory, immutable body and receipt. Archives were not executed; only bounded regular TeX members or decompressed text were read. TLS verification remained enabled.

`inputs.before.sha256` and `inputs.after.sha256` bind every discovery-lane file and the three governing AGENTS.md files. `logs/input-verification.log` records the final check. The candidate's input SHA-256 is **108c9239e48594895cdc0b943abf4334cf9e1006a63de5702a174ffad8cb15bd**, matching TASK.txt. Hash lists use workspace-relative paths. Run `./replay.sh` to verify the bound inputs and reproduce the independent calculations; every replay writes a fresh log.

Source references below are **original TeX line numbers**, not rendered PDF lines. Fresh v1 source bodies were byte-identical to discovery `sources/tex/2311.03257/main.tex` and `sources/tex/2312.08382/main.tex`; see `logs/inspect.log`. Fresh copies are `http/20261105T094148523877Z/text/main.tex` and `http/20261105T094148856266Z/text/main.tex`. The two live abstract pages (`http/20261105T094042959336Z/body`, line 165; `http/20261105T094042985419Z/body`, line 161) list only v1. Thus there is no unreviewed arXiv v2, but a journal revision remains possible.

## A. Statement fidelity — QUALIFIED_PASS

Exact authors: **Vladimir Gurvich and Mariya Naumova**. Exact titles: *GM-rule and its applications to impartial games*, arXiv:2311.03257; *Screw discrete dynamical systems and their applications to exact slow NIM*, arXiv:2312.08382. Authors appear at first-source lines 94 and 106 and second-source lines 96 and 108. The latter has a different earlier working title in the 2311.13511 bibliography; do not mistake that for a different conjecture.

Conjecture 1, verbatim in both sources (first lines 1139–1142; second 1777–1780):

> The set of $\ell$ GM-strategies form a (uniform) Nash equilibrium.

The precise game rules are first-source lines 1106–1133 and second-source lines 1744–1771. They specify a nonnegative integer n-vector; fixed cyclic player order; one kept entry and reduction of the other n−1 entries by one, conditional on the reduced entries being positive; at least two nonpositive entries terminate play; the next player loses. Length L(P) counts moves. C must exceed **every** possible play length from the same initial position. The loser pays C−L(P); each other player receives (C−L(P))/(ℓ−1). In the nonnegative game, “nonpositive” is exactly zero. The sources do not impose distinct entries, a divisibility hypothesis, or an initial-position restriction in this game subsection.

The GM choice is the minimum value divisible by ℓ, with the **rightmost** tied occurrence kept (first-source 185–200; second-source 184–207). The source's explicit no-multiple clause is first-source 1135–1137 and second-source 1773–1775: keep a largest entry, decrease the rest. Rightmost selection among equal maxima follows the general second-source tie-break. Every such equal-value choice gives the same successor multiset.

A potential objection is expressly answered by first-source 212–226: the dynamical-system discussion normally assumes a multiple exists, **except Section s-games**, which contains this conjecture. That assumption cannot be imported to invalidate (4,4,5). The second paper also permits multiple-free positions generally. The convention-free (5,5,6) witness independently disposes of this objection.

“Uniform” means independence from x⁰ (first 1144–1148; second 1782–1785). The papers do not supply a separate formal Nash definition. The standard literal reading is absence of a profitable unilateral strategy change against the other fixed strategies, from every initial position. The deviation here is positional and legal everywhere after extending it by GM, so it also refutes equilibrium when arbitrary history-dependent deviations are allowed. One need not make a claim about existence of other Nash equilibria.

Parameter scope: ℓ≥2; for the game k=n−1 with 0<k<n, n≥2 (second-source 184). The counterexample uses n=ℓ=3, safely inside every stated game domain. The n=1 infinite zero-removal process is not a finite game endpoint and should be omitted from the candidate's “trivial n≤2” discussion. For n=2 all plays have the fixed length sum(x), so strategies are immaterial.

Both sources explicitly identify ℓ=2 as already following from GMMV23 (first 1150–1151; second 1787–1788). GMMV23 is **Gurvich, Martynov, Maximchuk, Vyalyi**, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, arXiv:2304.06498. Its abstract at TeX 94–124 and M-rule/remoteness treatment around 242–319 concern two players, winning fastest and losing slowest. Neither primary conjecture paper states an ℓ≥3 counterexample. Do not confuse their integer-dynamics tables with multiplayer equilibrium computations.

MathDB comparison: discovery `raw/360653.jsonl:1` accurately includes the payoff and largest-entry completion. `raw/361128.jsonl:1` omits the payoff but cites the identical source paragraph; the payoff must be restored in the literal endpoint, rather than silently substituting a binary win/loss game. `results.json:2–31` and `32–60` refer to the same mathematical claim. Recommend the earlier, more explicit record 360653 for any eventual credit and a duplicate-resolution note for 361128.

Qualification: the DAM 2024 version of record, DOI **10.1016/j.dam.2024.07.018**, remains unread. ScienceDirect was pre-denied and was not requested. A journal withdrawal, correction, or replacement of the conjecture would matter to novelty and historical status, especially for 361128. The arXiv claim itself is unambiguous; journal uncertainty is not a mathematical defense of it.

## B. Independent mathematics — PASS

Implementation: `scripts/check.py:7–43` implements terminality, every legal move, sorted successor, rightmost GM, exact rational payoff, and best response. It imports no discovery code. Sorting is sound because the rules, rewards, and GM kept **value** are invariant under permutations; any sorted deviation can be implemented by choosing an actual pile of that value. No negative pile or illegal saturated subtraction is allowed. Sum decreases by n−1 on each legal move, making the finite search acyclic.

The independently reproduced paths from (4,4,5) are:

* GM: (4,4,5) → (3,3,5) → (2,3,4) → (1,3,3) → (0,2,3) → (0,1,2) → (0,0,1).
* P0 keeps a 4 first, then everybody uses GM: (4,4,5) → (3,4,4) → (3,3,3) → (2,2,3) → (1,1,3) → (0,0,3).

Their lengths are 6 and 5; losers are P0 and P2. Every play from this position has length at most floor(13/2)=6, so **C=7 is admissible**, not just larger than these two lengths. P0's payoffs are −1 and +1. For every admissible C they are −(C−6) and (C−5)/2. This is a strict unilateral improvement. The deviation “keep a minimum pile at x⁰, otherwise GM” is globally legal at nonterminal positions and positional; x⁰ never recurs since sum strictly decreases.

At (5,5,6), all-GM play has length 8, loser P2, and every nonterminal position on that baseline contains a multiple of 3. The separate minimax in `check.py:49–61,79–94` lets opponents choose **any legal move** at multiple-free states, independently at every visit. At P0 turns it maximizes exact payoff. With C=9 (admissible since sum=16), the baseline payoff is 1/2 and the worst payoff under one extracted policy is 1. Exhaustively traversing that policy's opponent branches gives only terminal pair (length,loser)=(7,1). The full policy tree and worst path are in `logs/check-final.json`, not just a selected favorable branch. The policy wins at length 7 for every completion, hence improves by 1/2 for every admissible C. Positions like (4,5,5) do lack a multiple **at an opponent's turn**: the discovery script's opening docstring saying otherwise is false. Its actual minimax computation, and the claimed robustness result, are nevertheless correct.

Independent exhaustive tests (`logs/summary.txt`, `logs/check-final.json`): all sorted starting positions with n=3, ℓ=2, entries≤12 (455 positions), and n=4, ℓ=2, entries≤8 (495 positions), with **every** possible deviator, give zero profitable deviations. For ℓ=3 the corresponding n=3, bound10 search (286 positions) finds 19 violating player-position pairs; n=4, bound7 (330 positions) finds 2. These are regression evidence, not proofs of the ℓ=2 theorem.

Correction: **(4,4,5) is not the smallest counterexample without qualification.** Our search finds (2,4,4): GM length5, P2 loses; P0 keeps2 first and then GM, length4, P1 loses. P0 wins both and improves by 1/2. Its sum10 is smaller than13. Keep (4,4,5) as the simplest exhibited **loss-to-win** witness; do not assert minimality of that subtype without a separate search specification/proof. See `check.py:78` and `logs/check-final.json:886` onward. This correction does not damage the general family.

### Independent general proof and attempted failure modes

Let n,ℓ≥3, a=(n−2)ℓ+1, b=(n−1)ℓ−1. Initially b>a, and both residues 1 and −1 are nonzero. GM keeps b. At time t_i=1+(i−1)ℓ, write q=(n−1−i)ℓ. The GM multiset invariant is

I_i = {q repeated n−i times, q+ℓ repeated i−1 times, q+ℓ−1}, 1≤i≤n−1.

For i≤n−2, q≥ℓ. Keep a q-valued entry for the next ℓ moves. After s moves, 1≤s<ℓ, the untouched-value representatives other than the kept q have values q−s, q+ℓ−s, and q+ℓ−1−s, with the appropriate multiplicities. None is divisible by ℓ except the last at s=ℓ−1, where it **equals q**. Switching between equal entries gives the same multiset, so rightmost ties do not break the argument. After ℓ moves the state is I_{i+1}. Before each reduction every reduced entry is positive: the smallest potentially reduced value is at least q−ℓ+1≥1. Thus no early terminal state occurs. At I_{n−1} the state is {0, ℓ repeated n−2 times, ℓ−1}. GM keeps the unique zero until the last entry reaches zero, precisely ℓ−1 moves later. Length =1+(n−2)ℓ+(ℓ−1)=(n−1)ℓ.

If P0 keeps a initially instead, the invariant at the same t_i is

J_i = {q repeated n−1−i times, q+1, q+ℓ−2, q+ℓ repeated i−1 times}.

For i≤n−2 there is a fresh q entry. The q+1 representative can first tie the pivot at s=1, the q+ℓ−2 representative at s=ℓ−2. These ties coincide when ℓ=3; all tied values are q, so even that collision is harmless. All remaining entries have nonzero residues during a block, and positivity has the same bound. At the next boundary the multiset is J_{i+1}. Finally J_{n−1}={1,ℓ−2, ℓ repeated n−2 times}. GM must keep an ℓ; one move produces a zero and an entry ℓ−3. If ℓ=3 there are already two zeros. Otherwise keep the sole zero for ℓ−3 more moves. Total length=1+(n−2)ℓ+1+(ℓ−3)=(n−1)ℓ−1. No phase assumes n>3 or ℓ>3; zero fresh-pile multiplicities at the last boundary are intentional.

The respective losers are P0 and P_{ℓ−1}, yielding a strict sign-changing improvement for all admissible C. This proves the candidate family, independently of the finite tests. `check.py:64–74` additionally checks every block boundary and terminal length for 3≤n≤15 and 3≤ℓ≤24 (286 pairs).

## C. Prior art — QUALIFIED_PASS, incomplete clearance

Live primary author listings were obtained for Gurvich and Naumova with up to 200 results, sorted newest first. The Gurvich page lists 62 results; Naumova's includes unrelated namesakes. `logs/screen.log` records every parsed title and full relevant listing entry. Relevant GM/exact-slow-NIM entries include the two targets, arXiv:2311.13511, and GMMV23. There is no listing entry identifying an erratum or multiplayer refutation. Absence from these lists is bounded evidence only.

The related arXiv:2311.13511 source describes **two players** at lines129–137, and its M-rule failure classification is for the **misère** remoteness function. It is not an ℓ≥3 equilibrium refutation. The later Games 2024 published abstract likewise says two players (https://doi.org/10.3390/g15060037; search located the published author PDF at https://www.econstor.eu/bitstream/10419/330106/1/games-15-00037.pdf). The related NIM(4,2)/NIM(5,2) working paper abstract found through search also concerns two players. That body was not independently fetched here, and is not used to claim comprehensive clearance.

Two spaced unauthenticated GitHub repository searches (well below the eight-query maximum) returned zero for `"exact slow nim"`, and one for `"Gurvich" "Naumova"`: **JD-Jones-ASES/gn-lean**. Current head is **73bb87b16da8c053fd07e0d4dc43732b74335a3b**, dated 2026-09-07. Its pinned README explicitly states a partition of [n] into sets of size≤3 whose sums are powers of3, arXiv:2508.00946v3. That theorem is unrelated to NIM; a shared author name is not overlap. README and head receipts are preserved.

Lean Pool current head from the required API endpoint is **01db1d7049cf9668bda1e9e106875ee1278b43e6**, dated 2026-10-07. The recursive tree was **not truncated**. The actual config path is **LeanPool/projects.yml**; an initial root-level path gave404 and was corrected. All substantive candidate queues/data (`discovered.yml`, `shortlist.md`, `manual.txt`, both queues, `decisions.jsonl`, `provenance.jsonl`) and the config were downloaded at that immutable head and screened for exact NIM, author names, arXiv identifiers and MathDB identifiers, with zero relevant hits. These are current fetches, not reuse of an old tree. Logs record the tested patterns and paths; no assertion of exhaustive semantic review of all Lean Pool code is made.

Web search queries were `"Gurvich" "Naumova" "GM" "Nash"`, `"GM-strategies" counterexample`, and `"exact slow NIM" "players" equilibrium`. They located the primary two-player papers and MathDB, with no public refutation. Search-index silence is weak evidence.

**Missing required evidence:** OpenAlex citing works for both targets could not be screened. An initial invalid `arxiv:` filter returned400; a corrected title query returned **429** (`http/20261105T094210661526Z/receipt.json`). No request to OpenAlex was made thereafter. The queued DOI request was locally blocked before network access, with its own receipt. Crossref, Semantic Scholar, arXiv search API and ScienceDirect were pre-denied and never requested. The successful arXiv queries used the HTML author-search pages, not the denied search API. Do not retry these hosts during this review. No claim of full novelty clearance is justified.

## D. Significance and exclusion screen — QUALIFIED_PASS

The result genuinely refutes the literal multiplayer conjecture: legal nonterminal positive initial positions, stated fallback, original payoff, fixed cyclic order, one player's positional deviation. There is no ℓ=2-only restriction to rescue it. The loss-to-win family does not rely on subtleties about preference for faster wins. It works for every n,ℓ≥3, rather than being a boundary correction. The second certificate shows that removing the fallback convention does not rescue the length-dependent equilibrium claim.

The papers' formulas compute **GM dynamics**; they do not assert an inequality comparing arbitrary unilateral deviations for ℓ≥3. I did not find the counterexample among the printed tables, nor a printed construction asserting it. The independent payoff comparison is additional to evaluating a printed GM trajectory. Nevertheless, the family is elementary and uses the same block mechanism as the source's dynamics. Root should explicitly adjudicate the campaign's stringent “evaluating the source's own formula / routine corollary” exclusion. I recommend treating this as an eligible small exact counterexample to a named conjecture, consistent with the stated precedents, provided novelty checks clear; I do **not** recommend exclusion solely because the witness is short. The all-n,all-ℓ theorem strengthens the dossier but cannot earn separate credits.

Qualification remains the unread journal version and incomplete citing-work screen. Do not self-accept or count either record yet.

## E. Cheapest literal Lean route — QUALIFIED_PASS

Use **one finite witness**, not the general family, for the cheapest exact negation. Define for every n≥2 and ℓ≥2:

1. Positions as Fin n→Nat (or sorted vectors with a proved correspondence), terminality as at least two zeros, legal kept index, and a move reducing exactly the other positive entries.
2. Legal positional strategies (legality required only at nonterminal positions); canonical deterministic GM with the source's rightmost tie-break; ℓ-player profile all equal to GM. A zero at a nonterminal position is unique and divisible by ℓ, proving GM legal.
3. A total play-length function terminating by sum(x), with proof that every legal move lowers sum by n−1>0. Alternatively fuel sum(x)+1 plus proof that valid profiles never exhaust it and a fuel-independence bridge. A raw Option result without these bridges is insufficient.
4. Outcome, loser t mod ℓ from initial player0, rational payoff exactly as in the paper, and admissible C meaning larger than every legal play length. Define IsNash as no **legal** unilateral positional deviation improving that payoff. State and document the embedding into history-dependent strategies, if those are used for the literal source endpoint.
5. Conjecture : Prop := ∀ n≥2, ∀ ℓ≥2, ∀ x⁰, ∀ admissible C, IsNash x⁰ C (GMProfile n ℓ). Prove ¬Conjecture by n=ℓ=3, x⁰=(4,4,5), C=7, and GM except for the initial minimum-pile choice. Include a named bridge theorem explicitly identifying the two legal plays and rewards and deriving ¬IsNash; do not stop at “length6 ≠ length5”.

This needs no general Nash-existence theory, imported game-theory library, or general periodicity formalization. A fixed source tie-break is enough: the candidate note at lines138–140 incorrectly says fidelity **requires** allowing every tie-break. The source actually fixes the rightmost rule. Quantifying all equal-value selections is optional and stronger, and then requires a selection-invariance theorem. Computation by `decide` or `rfl` cannot directly evaluate an arbitrary function variable σGM; either instantiate the actual deterministic function or rewrite its constrained choices first.

Assessment of the uncompiled draft (`CANDIDATE-360653-361128.md:106–143`): it is a sketch, not a nearly complete certificate. At line130, `Nat.mod_lt _ (by omega)` has no hypothesis 0<l, and cannot hold for arbitrary l. At lines127–131, legality is never checked; arbitrary strategies with saturated subtraction need not terminate as the game does. Payoff, admissibility, profile update, Nash, conjecture, all bridges, and the actual refutation are only comments. The endpoint also omits the n≥2 finite-game restriction. Its relational GMSel requires choices even at terminal states, which is harmless but adds unnecessary obligations. None of this falsifies the mathematical route, but it invalidates the “only evaluate two plays” cost estimate.

Estimated cost: a few hundred lines of elementary Lean, with most work in legal strategies and total-play bridges; moderate rather than zero effort. The explicit witness arithmetic is cheap. Formalizing the general family is optional and substantially more work (multisets, block induction, boundaries). Use the pinned Lean4.34.1/mathlib environment, no sorry/admit/added axioms/unsafe/native_decide, and check endpoint transitive axioms against propext/Classical.choice/Quot.sound. Every Lean invocation must use the lane watchdog and -M3500. A clean extracted rebuild remains an acceptance prerequisite, not an output of this pre-investment review.

## Required next evidence and corrections

Maintain HOLD until root has (i) an authorized non-retry route or already-held evidence sufficient to screen citing works of both papers, including later errata, and (ii) a reliable determination of whether the DAM version retains, modifies, or withdraws the conjecture, or a documented root decision accepting 360653 despite that publication-status gap. Do not evade the current network denials. Correct the minimality claim, the convention-free script docstring, the n=1 discussion, and the Lean cost/definition gaps during packaging. Those corrections are local and do not require another discovery search. Once cleared, proceed with the finite literal Lean endpoint and its independent kernel/statement review, one credit at most. This review makes no acceptance decision.
