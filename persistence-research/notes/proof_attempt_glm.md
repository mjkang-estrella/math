# Proof attempt: the deepest 1-insertion families, via a memory-bounded BCGN cascade

> **ERRATUM (parent audit, 2026-10-19):** Theorem E as stated is false — (★δ) omits the
> prime 5, and F₅ contains the 7-smooth members **5 and 15**. Corrected (proved): F₅'s
> 7-smooth members are exactly {5, 15}; see verification/REPORT.md and
> verification/v8_delta5.py. Table 1's δ=5 row should read {5, 15}.

**Round 2 (GLM sub-agent), resumed after an OOM kill.** Every claim labelled
PROVED / COMPUTED / CONJECTURAL. Artifacts in `verification/glm/` (see §7);
reproduce everything with `bash verification/glm/run_all.sh` (~5 min, every
python invocation capped at `ulimit -v 3000000`).

---

## 0. What this document is

The audit (verification/REPORT.md) reduces the conjecture to explicit 1-insertion
family decisions (Theorems D–F of notes/pure_math.md). The **deepest layer** of that
reduction — never decided by anyone — is:

> **Family F_δ** (δ = 1,…,9): all n = R_L + (δ−1)·10^e, L ≥ 1, 0 ≤ e < L — decimal
> strings of 1s with exactly one digit replaced by δ. These are exactly the
> Π-preimages of a terminal single digit δ whose digit multiset is {δ} ∪ {1s}:
> the last multi-digit level m₁₀ → m₁₁ = δ of a hypothetical persistence-12 chain
> (chain indexing of notes/pure_math.md, Theorem B).

A 7-smooth member n of F_δ satisfies

  (★δ)  9n = 10^L + 9(δ−1)·10^e − 1 = 2^t · 3^(u+2) · 7^w

with t = v₂(9n), u+2 = v₃(9n), w = v₇(9n). Round 1 built a BCGN-style modular
cascade (m₁₂ → m₂₄ → m₄₈ lifting, cf. arXiv:2110.04263) for (★δ) and died of an
8 GB RSS blow-up in stage 2. This round: (i) re-certify stages 0–1 exactly against
the round-1 pickle, (ii) redesign stage 2 as a memory-bounded *streaming* sieve
(peak RSS 14 MB where round 1 needed ~8 GB), (iii) convert survivors into exact
finite checks ("phantom handling", §3), (iv) independent certificates (§5).

**Headline results.**
- **Theorem E (complete family decision):** F₅ contains **no 7-smooth member for any
  number of inserted 1s** — proved by a finite mod-M₀ certificate (144 residues,
  none in the 8,910,000-element image set; two independent implementations).
  Likewise **F₁'s only 7-smooth member is n = 1, for all L** (Zsigmondy; no
  computation needed).
- **Theorem R (bounded-length complete decision):** for each δ ≠ 5, the 7-smooth
  members of F_δ with at most **10⁷ digits** are exactly the 1–4 small numbers of
  Table 1 (all ≤ 3 digits); every candidate class beyond them is killed by an
  exact-integer check. Cross-validated against a fully independent enumeration
  to L ≤ 3000 with *exact* agreement in (L, e, t, u, w).
- **Lemma 1, Lemma 2 (PROVED, elementary):** t ≥ 1 ⟹ e = 0; and the sharp uniform
  bound t ≤ t_max(δ) = (0,4,0,2,0,4,0,3,0)[δ], proved here by a two-line case
  analysis — no dependence on the (unrefereed) Fonga preprint for these families.

## 1. Setup

Moduli M_K = (10^(12·2^K) − 1)/189: M₀ = 5291005291 = 11·13·37·101·9901,
M₁ = M₀·73·137·99990001 = (10²⁴−1)/189, M₂ = M₁·17·5882353·9999999900000001
= (10⁴⁸−1)/189. 2, 3, 7 are units mod M_K. Re-verified this round (glm2 asserts +
standalone check):
ord_{M₀}(3) = 9900, ord_{M₀}(7) = 900, ord_{M₀}(10) = 12; ⟨3⟩∩⟨7⟩ = {1} mod M₀
(so the representation V ≡ 3^U·7^W (mod M₀), 0 ≤ U < 9900, 0 ≤ W < 900, is
**unique** — this makes round 1's stage-0 lookup sound);
ord_{M₁}(3) = 849915000 = O₃₁, ord_{M₁}(7) = 673200 = O₇₁;
stage-2 primes p | 10²⁴+1 with period pairs (s₃, s₇) = (ord_p(3)/gcd(ord_p(3),O₃₁),
ord_p(7)/gcd(ord_p(7),O₇₁)): p=17: (2,1); p=5882353: (122549,17507);
p=9999999900000001: (100010000, 252525250000), and p−1 = 2⁸·3²·5⁸·11·73·101·137
is smooth, so Pohlig–Hellman applies (largest subgroup 5⁸ = 390625, BSGS ≤ 627 steps).

**Lemma 1 (PROVED).** If (★δ) holds with t ≥ 1 then e = 0.
*Proof.* For e ≥ 1, 10^L + 9(δ−1)10^e − 1 ≡ −1 ≡ 1 (mod 2), while 2^t·3^(u+2)·7^w
≡ 0 (mod 2) for t ≥ 1. ∎

**Lemma 2 (PROVED, elementary).** For every member of F_δ, t ≤ t_max(δ) with
(t_max(1),…,t_max(9)) = (0,4,0,2,0,4,0,3,0).
*Proof.* If δ is odd then 9(δ−1)10^e is even, so 9n is odd and t = 0. If δ is even,
Lemma 1 gives e = 0 whenever t ≥ 1, and then 9n = 10^L + D_δ with D_δ = 9(δ−1)−1 ∈
{8, 26, 44, 62}. Writing D_δ = 2^a·d (d odd), for L > a we get
10^L + D_δ = 2^a(2^{L−a}5^L + d) with odd bracket, so v₂ = a; the finitely many
L ≤ a give v₂ ≤ 4, attained only at (δ, L) = (2, 3) [1008 = 2⁴·63]. Sup over L:
δ=2: 4, δ=4: 2, δ=6: 4, δ=8: 3; δ odd: 0. ∎ (This matches Fonga's 𝔙 recursion —
arXiv:2608.27802 Thm 4.1 — run on {δ}, which vunga.py implements and which this
round re-validated against brute force on 23 digit multisets; the sieve below uses
only the elementary proof.)

**Size bounds.** Any solution of (★δ) satisfies 10^L − 1 ≤ 2^t·3^(u+2)·7^w <
8.2·10^L (as 0 ≤ e ≤ L−1, δ ≤ 9), hence u+2 < log₃(8.2·10^L) ≈ 2.0959·L + 1.92
and w < log₇(8.2·10^L) ≈ 1.1833·L + 1.08.

## 2. The cascade (stages 0–2) and its soundness discipline

Stage K fixes (L, e) mod 12·2^K and (u+2, w) mod (O₃K, O₇K) consistently with (★δ)
mod M_K. A **survivor class** at stage 2 is

  C = (L₄₈, e₄₈, t, U₁, W₁, k_u mod κ_u, k_w mod κ_w),

meaning any solution of (★δ) in this class has L ≡ L₄₈, e ≡ e₄₈ (mod 48), t = t
exactly, u+2 = U₁ + O₃₁·k_u with k_u ≡ κ-residue (mod κ_u) and k_u ≥ 0, and
w = W₁ + O₇₁·k_w with k_w ≡ κ-residue (mod κ_w), k_w ≥ 0. The big-prime congruence
3^{O₃₁k_u}7^{O₇₁k_w} ≡ V·(3^{U₁}7^{W₁})^{−1} (mod 9999999900000001) is solved by
Pohlig–Hellman and applied through its **projection onto k_u** (necessary condition
k_u ≡ x₀ mod P, P = gcd(b,N)/gcd(a,gcd(b,N)) — sound, lossy; the loss is immaterial
because κ_w ≥ 17507 already pins w for all L considered). The mod-M₁ and mod-M₀
parts are carried by (U₁, W₁) since 3^{O₃₁} ≡ 1, 7^{O₇₁} ≡ 1 mod M₁.

**Soundness rule (enforced in code).** At every stage, every *enumerated* member's
class must survive; stage-0 and stage-1 outputs are additionally asserted **equal**
to round 1's level1_results.pkl for all 9 δ (exact match). The stage-2 stream count
for δ=7 (297,619 classes) matches round 1's materialized count exactly.

**Round-1 stage 0/1 results (reproduced exactly):** per δ, (t_max, |members L≤40|,
|s₀|, |s₁|) = δ=1: (0,1,12,408); δ=2: (4,4,7,85); δ=3: (0,1,3,34); δ=4: (2,2,3,51);
δ=5: (0,0,**0**,0); δ=6: (4,2,4,34); δ=7: (0,1,1,17); δ=8: (3,3,4,68); δ=9: (0,1,2,34).

## 3. The pinning argument (replaces the OOM'd stage 2)

**Theorem P (pinning; PROVED).** Let C be a stage-2 survivor class with periods
P_u = O₃₁·κ_u and P_w = O₇₁·κ_w. Both κ's are bounded below *uniformly*: every
yielded class carries the p=17 and p=5882353 constraints, so κ_u ≥ lcm(2, 122549)
= 245098 and κ_w = 17507, giving P_u ≥ 2.08·10¹⁴ and P_w = 1.1785·10¹⁰ for every
class. Let
U₂ = least element ≥ 2 of {U₁ + O₃₁(κ_u-residue + κ_u·j) : j ≥ 0} and W₂ = least
element ≥ 0 of the w-progression. If L ≤ L_check with u_cap any safe integer
upper bound for (log₁₀8.2 + L_check)/log₁₀3 (the code uses ⌊·⌋+3) satisfying
u_cap < P_u, and likewise w_cap < P_w, then every
solution of (★δ) in C with L ≤ L_check has **exactly** t = t, u+2 = U₂, w = W₂.
Moreover such a solution exists iff for some candidate length L with L ≡ L₄₈ (mod 48),
1 ≤ L ≤ L_check and 10^L − 1 ≤ N₀ < 8.2·10^L (N₀ := 2^t·3^{U₂}·7^{W₂}), the integer
N₀ equals 10^L + 9(δ−1)10^e − 1 with e ≡ e₄₈ (mod 48), 0 ≤ e < L — an exact
big-integer check on at most 5 candidate lengths (those within ±2 of
S = t·log₁₀2 + U₂·log₁₀3 + W₂·log₁₀7, computed in floats with 10⁻⁶ slack; each
candidate is decided exactly: D := N₀ + 1 − 10^L must be 0 (δ=1) or satisfy
D > 0, D ≡ 0 mod 9(δ−1), D/9(δ−1) = 10^e with the e-congruences).

*Proof.* k_u ≥ 0 and k_u ≡ residue (mod κ_u) force k_u = residue + κ_u·j, j ≥ 0,
so u+2 ∈ {U₂ + P_u·j}. If j ≥ 1 then u+2 ≥ P_u > u_cap ≥ u+2 — contradiction; hence
u+2 = U₂ (and a solution requires U₂ ≤ u_cap, else the class is dead for
L ≤ L_check). Identically w = W₂. Given (t, u+2, w), the size window pins L to
within ±1 of S; the float computation of S is accurate to ~10⁻⁹ ≪ 1, so the ±2
candidate window covers all cases, and each candidate is checked exactly. ∎

**Consequence.** With L_check = 10⁷: u_cap ≈ 2.1·10⁷ < P_u and w_cap ≈ 1.19·10⁷ <
P_w **unconditionally** (the inequalities hold for every class). Hence the pinned
checks give the **complete** list of 7-smooth F_δ members with L ≤ 10⁷ (Table 1).
The same argument is sound for any L_check ≲ 10⁹ (the binding period is P_w;
P_u binds only near 10¹³); beyond that, per-class periods must be checked before
pinning. The *practical* limit is the phantom count, which grows ∝ L_check.

**Theorem E (δ = 5; PROVED, complete for all L).** F₅ contains no 7-smooth member
for any number of inserted 1s. *Proof.* Every member is odd (R_L odd, 4·10^e even),
so t = 0, and 9n = 3^{u+2}7^w forces 10^L + 36·10^e − 1 ≡ 3^U 7^W (mod M₀) for some
(U, W). The 144 values (L mod 12, e mod 12) are **none** in the image set
{3^U 7^W mod M₀} — verified by two independent implementations (glm2.stage0
meet-in-the-middle: |s₀| = 0; delta5_certificate.py: explicit 8,910,000-element
set, 0 hits). So no member is 7-smooth for any L ≥ 1, 0 ≤ e < L. ∎

**Corollary E′ (δ = 1; PROVED, complete for all L — pure thought).** The only
7-smooth member of F₁ is n = R₁ = 1. *Proof.* For n ≥ 2, (10,1,n) is not a
Zsigmondy exception (10+1 = 11 is not a power of 2), so R_n has a primitive prime
divisor q with ord_q(10) = n, whence n | q−1 and q ∉ {2, 3, 5}; 7-smoothness of
R_n forces q = 7, so n | 6, and R₂ = 11, R₃ = 3·37, R₆ = 3²·7·11·13·37 are not
7-smooth. ∎ (Agrees with the sieve verdict for L ≤ 10⁷ — an independent
mutual validation.)

**Why no class can be killed outright for all L (honesty check).** For a surviving
class, S(t, u+2, w) = S₀ + j·P_u·log₁₀3 + l·P_w·log₁₀7 with j, l ≥ 0; since
log₂, log₃, log₅, log₇ are ℚ-linearly independent, {(j·P_u·log₁₀3 +
l·P_w·log₁₀7) mod 48} is dense, so the size window is hit for arbitrarily large L:
size arguments alone never finish a class. The cascade gives *bounded-length*
completeness (Theorem R); *unbounded* completeness needs deeper stages (each stage
squares the reachable length), effective S-unit bounds, or the full BCGN tree
machinery. δ = 5 is the exception because its stage-0 classes are **all** dead.

## 4. Round-1 post-mortem (memory)

Instrumented probe (this round): δ = 7 — 17 stage-1 survivors → 68 positions →
**297,619 survivor dicts** (~300 MB as Python dicts with embedded congruence
tuples). δ = 1 scales to 1632 positions → ≈ 1.4·10⁷ dicts ≈ 8 GB ⇒ the OOM.
Fix: the stage-2 refinement is a **generator**; classes are consumed one at a time
by the pinning checker; O(1) memory. Measured peak RSS for δ = 1 (14,285,712
classes streamed): **14 MB** (cap 3072 MB), 17 s wall. One additional trap found
(the hard way, in δ=2): the position class with V ≡ 0 (mod 9999999900000001)
makes the dlog-based filter crash unless recognized as dead — 3^{u+2}7^w is a
unit mod p, so V ≡ 0 is simply unsolvable and the position dies. A second,
latent round-1 bug: `minimal_n_bound` in stage2.py added O₃₂ (not the true class
period O₃₁·κ_u) when bumping u+2 past its minimum, overstating the minimal-n
bound (unsound) in the corner case U₁ < 2; glm2.py computes the true least valid
element instead.

## 5. Results

**Stage statistics** (L_check = 10⁷; every run `ulimit -v 3000000`, all < 3 GB,
slowest 17 s):

| δ | positions | classes streamed | dead by u-bound | pinned | member classes | dead pinned (phantoms) |
|---|---|---|---|---|---|---|
| 1 | 1632 | 14,285,712 | 14,285,664 | 48 | 1 (47 dup classes) | 0 |
| 2 | 340 | 1,488,095 | 1,488,090 | 5 | 4 | 1 |
| 3 | 136 | 595,238 | 595,236 | 2 | 1 | 1 |
| 4 | 204 | 892,857 | 892,854 | 3 | 2 | 1 |
| 5 | 0 | 0 (s₀ = ∅) | — | — | — | — |
| 6 | 136 | 595,238 | 595,236 | 2 | 2 | 0 |
| 7 | 68 | 297,619 | 297,618 | 1 | 1 | 0 |
| 8 | 272 | 1,190,476 | 1,190,472 | 4 | 3 | 1 |
| 9 | 136 | 595,238 | 595,236 | 2 | 1 | 1 |

(δ=1: 47 duplicate class variants all re-derive the same solution — the code
asserts they agree on (t, u, w).)

**Table 1 — the complete list of 7-smooth members of F_δ with L ≤ 10⁷ (COMPUTED;
cross-validated against an independent enumeration to L ≤ 3000 with exact
agreement in (L, e, t, u, w); every entry re-certified by direct construction +
digit-string check + exact factorization, verify_members.py):**

| δ | members n = R_L + (δ−1)10^e | (L, e ; t, u, w) |
|---|---|---|
| 1 | 1 | (1, 0 ; 0, 0, 0) |
| 2 | 2, 12, 21, 112 | (1,0;1,0,0), (2,0;2,1,0), (2,1;0,1,1), (3,0;4,0,1) |
| 3 | 3 | (1, 0 ; 0, 1, 0) |
| 4 | 4, 14 | (1,0;2,0,0), (2,0;1,0,1) |
| 5 | **none — for ALL L (Theorem E)** | — |
| 6 | 6, 16 | (1,0;1,1,0), (2,0;4,0,0) |
| 7 | 7 | (1, 0 ; 0, 0, 1) |
| 8 | 8, 18, 81 | (1,0;3,0,0), (2,0;1,2,0), (2,1;0,4,0) |
| 9 | 9 | (1, 0 ; 0, 2, 0) |

Notably: **no member at all has 4 ≤ L ≤ 3000 for any δ** (independent enumeration),
and the sieve extends that emptiness to L ≤ 10⁷.

**Phantoms (classes that survive every congruence and the size window but fail the
exact equation; all re-checked on a widened window):** δ=2: (L≡0, e≡0 mod 48;
t=0; 9n=9); δ=3: (L≡1, e≡1; 9n=27); δ=4: (L≡0, e≡0; 9n=27); δ=8: (L≡0, e≡0; 9n=18);
δ=9: (L≡1, e≡1; 9n=729). These are "ghosts" of other families' members (e.g. 729 =
9·81, with 81 ∈ F₈) appearing in a foreign δ's residue classes — the pinning check
kills each one exactly.

**Corollary (chain application; PROVED modulo Theorem R's L ≤ 10⁷ qualifier).** In
a hypothetical persistence-12 chain (m₀ → … → m₁₁), the level-10 node m₁₀ (which
must be 7-smooth, ≥ 2 digits, with Π(m₁₀) = m₁₁ = δ a single digit) — *if its digit
multiset is {δ} ∪ {1s}* — is one of {12, 21, 112, 14, 16, 18, 81} whenever it has
≤ 10⁷ digits. The backward tree above these seven nodes (multisets {2,2}, {2,3},
{3,4}, {2,2,3}, … plus 1s) is the next layer and is within reach of the same
machinery (the position grid gains one coordinate per exceptional digit).

## 6. Honest limitations

1. Theorem R is a **bounded-length** decision (L ≤ 10⁷). Members with more than 10⁷
   digits are not excluded — heuristically none exist (the expected number of
   7-smooth members in a 1-insertion family decays super-exponentially in L),
   but this is CONJECTURAL. The same proof is sound for any L_check ≲ 10⁹
   (P_w = 1.18·10¹⁰ is the binding period); the obstacle beyond that is the
   growing number of pinned phantom classes that must be exact-checked, not
   soundness.
2. The big-prime congruence is used only via its k_u-projection; tracking the joint
   (k_u, k_w) class would strengthen the sieve but changes nothing here (κ_w ≥
   17507 already pins w far beyond any L_check used).
3. Bounded-length family decisions do **not** close the conjecture: a hypothetical
   chain could pass through a member with > 10⁷ digits (or through higher layers
   with several exceptional digits). What this round *does* establish: the deepest
   layer of the even-terminal-digit antecedent trees (BCGN's open case) is now
   explicit, finite, and — for δ = 5 — completely closed.
4. t ≤ t_max is self-contained here (Lemma 2, elementary). For multi-digit
   exceptional multisets one would need Fonga's 𝔙 (validated but unrefereed) or an
   independent proof.

## 7. Artifacts (verification/glm/)

- `glm2.py` — self-contained cascade: constants+asserts, stage 0 (meet-in-the-middle,
  O(1) mem), stage 1 (port of round 1), stage 2 **streaming generator** + pinning
  checker (`check_stream`), driver `--delta D --lcheck 10^7`. Peak RSS 14 MB.
- `enum_members.py` — independent direct enumeration to L ≤ 3000 (exact big-int
  trial division; checkpointed JSONL per δ).
- `verify_members.py` — certificate: every reported member re-derived from (L, e)
  and verified (digit string, exact 7-smoothness, valuation match); every phantom
  re-checked on a widened window; enum-completeness assert.
- `delta5_certificate.py` + `delta5_certificate.json` — Theorem E certificate
  (explicit image set, 144 residues, 0 hits).
- `results_delta{1..9}.json` — per-δ results: s0, s1, stats, members, phantoms.
- `members_delta{1..9}.jsonl` — raw enumeration output.
- `run_all.sh`, `run_all_log.txt` — reproducible pipeline + captured log.
- `vunga.py` (round 1) — Fonga 𝔙; re-validated this round (23 multisets, ALL OK).
- `level1_results.pkl`, `cascade.py`, `stage2.py`, `run_level1*.py` — round-1
  artifacts, kept for the record; stage0/1 reproduced exactly by glm2.py.
- `notes/proof_attempt_glm.md` — this document.
