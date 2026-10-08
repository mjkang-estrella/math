# H027 walk review — raw Opus report

2026-10-08. RAW independent review. Strong rejection/constant claims are NOT accepted pending scope reconciliation. No primary PDF was read by this reviewer.

# H027 low-memory walk review: all three cards fail on paper

**Verdict.** No experiment is needed to decide any of the three cards; all three fail on paper. Verified ECDLP improvement remains **NONE**, and the square-root reference is unchanged.

I made no edits, ran no experiments and started no child agents. Besides the supplied report, I read only `research/findings/H023-fixed-difference-walk.md`. That note already leaves the useful-collision constant open ("Only assuming equal useful-collision constants…"). The argument below settles that open premise against these cards.

**Source access.** `eprint.iacr.org/2011/003.pdf` returned HTTP 403. My guessed `cr.yp.to` mirror returned 404. No primary PDF was read in this review. These sources are cited from memory:
- Bernstein–Lange–Schwabe, PKC 2011: negation constant √(πq/4) ≈ 0.886√q, a walk that must be well defined on {±P}, and fruitless 2-cycles at rate about 1/(2r).
- Brent–Pollard 1981: collision time grows as 1/√Var(indegree).
- Teske 1998/2001: mixed walks that include squaring/doubling branches, and r-adding walks with a factor √(r/(r−1)).

Treat these constants as unverified against the PDFs.

## 1. The negation constant does not apply to this detection rule (all cards)

The successor function is defined on the point P, not on the class {±P}:
- The fill is not negation-equivariant: f(−P) = −P+G, which differs from −(P+G).
- Doubling and tripling are equivariant, and a bucket rule based on x is ±-invariant. Neither fact helps, because one non-equivariant branch is enough to break equivariance.

So walkers at P and −P separate on the next fill and never coalesce.

Hashing x alone catches a ±P coincidence only when both points are themselves stored distinguished points. Take distinguished fraction θ and N total steps. The expected number of such stored pairs is about θN²/(2q). That needs N ≈ √(2q/θ) ≈ q^{5/8} at θ ≈ q^{-1/4}, so these hits are negligible.

The applicable baseline is therefore the full-group rho constant √(πq/2) ≈ 1.2533√q, not 0.886√q. On its own this costs a factor of √2.

Repairing equivariance needs a sign-dependent step, P ↦ P + σ(P)G with σ(−P) = −σ(P). That is exactly H023's reflection-quotient ±G rule, an r=1 additive walk. Its fruitless 2-cycles occur with probability about 1/2 per step. The oriented state cannot both keep the cheap fill and recover the negation factor.

## 2. The decisive kill: the fill is a bijection, so coalescence is rare

Write f(P) = P+G off the bucket and f(P) = 2P (or 3P) on the bucket B, which has density δ. Both branches are bijections on Z/q. A point R has:
- the preimage R−G when R−G ∉ B (probability 1−δ);
- the preimage R/2 when R/2 ∈ B (probability δ).

The indegree therefore has variance 2δ(1−δ). Two trails merge only through an indegree-2 point. By the Brent–Pollard heuristic, which also gives Teske's r-adding factor:

  E[steps] ≈ √(πq/2) / √(2δ(1−δ)).

At δ = 1/32, 2δ(1−δ) = 0.0605, so the penalty is 4.06× and E[steps] ≈ **5.09√q**. The card assumed 0.886√q.

| Card | Per-step cost (S/M=1) | Expected work | Ratio to negation rho (0.886·6 = 5.317) |
|---|---|---|---|
| 1 (doubling) | 5.281 | 26.9√q | **5.06×** |
| 3 (tripling) | 5.719 | 29.1√q | **5.48×** |

The card's slack was 13.6% for Card 1 and 5% for Card 3, so a heuristic error of even 2× would not change the verdict.

**No choice of δ rescues the cards.** Card 1 costs 5 + 9δ per step. The function (5+9δ)/√(2δ(1−δ)) has its minimum ≈ 11.8 near δ ≈ 0.27. Total work is then about 14.8√q, still **2.8×** rho.

**General gate.** Any oriented walk of this class with average per-step cost c beats negation rho only if

  c < 4.24·√(2δ(1−δ)) ≤ 3.0 M-equivalents.

The 5M fill alone fails this.

**Scope of the kill.** It covers walks made of a fixed-translation fill plus a state-selected mixer, with oriented detection. It is not a general lower bound for low-memory walks.

The same law also kills a phase-free version of Card 2, f = P+G off the bucket and P+J_h on it. Its jump costs O(log q), so δ must be about 1/log q, and the penalty grows like √(log q).

## 3. Card 2: the phase counter costs a factor of r

The walk state is (P, c). Two walkers at the same P with different phases jump from different points and separate. Point coincidences therefore count only when the phases match, which happens with probability 1/r.

Detection then reduces to collisions of the macro-walk, a 16-adding walk with jumps rG + J_h. Total fills come to about

  r · 1.2533 · √(16/15) · √q ≈ 1.29·r·√q.

At q ≈ 2^16 with r = 64 that is about 83√q, and the penalty grows like 4·log₂q. This holds whether the phase is a global clock or per-walker. Any restart that desynchronizes the phase makes it worse.

There is also a minor cost the card omits: choosing the sign of y needs one extra x(P−G)-type evaluation per macro step.

## 4. Other charges the report omits or gets wrong

- **Null relations (Card 1).** All starts are [s_i]G+Q with b = 1. The "pure-G walker" in the recovery text does not exist in the operations list, so the card contradicts itself.
  - A merge 2P₂ = P₁+G gives the k-coefficient 2^{e₁} − 2^{e₂+1}, which is null when e₁ = e₂+1.
  - "Discard and continue" is wrong. Merged walkers stay identical and repeat the null forever. One walker must be restarted with a fresh scalar multiplication, and its lost trail must be charged.
  - At toy scale the null rate is large. With 64 walkers each walker takes about 20 steps, for a mean depth of about 0.6.
- **Memory.** A full x-only BSGS fallback needs √q storage. That violates the q^{1/4} envelope and imports the very high-memory method the card excludes.
  - The predicted 5.09√q exceeds the 4√q cap, so most runs would fall back.
  - The proposed "median useful-hit count" is then undefined or censored.
  - Replace the fallback with a Las Vegas restart and charge it in full.
- **Distinguished-point trails.** Storage of q^{1/4} implies θ ≈ q^{1/4}/N, and in-flight trail overhead is about W/θ.
  - With W = 64 at q = 2^16 (q^{1/4} = 16), overhead is about 4N. That toy protocol measures trail waste, not collisions.
  - The distinguished-point rule is never specified. It must be independent of the x mod 32 bucket bits, for example a hash of x.
- **Costs (spot checks).**
  - Card 1's doubling cost of 11M+3S matches H023 (2M+2S+I plus 3M+S+I, batched).
  - Card 3's tripling audits to about 10M+4S+4I, or about 22M+4S batched. The card says 24M+4S. The difference is immaterial.
  - The Card 2 square root at about 1.5·log₂p for p ≡ 3 mod 4 is fine.
- **Novelty.** Card 1 is a Teske-style mixed walk: an r=1 adding walk plus a doubling branch. Card 2 is an r-adding walk with a forced translation run. Neither is new. H023 already holds the formulas.

## 5. Corrected hypothesis (replaces all three cards)

**H027-W.** For an oriented walk in which a fraction 1−δ of steps is a fixed-translation bijection, useful coalescence per step-pair happens at rate about 2δ(1−δ)/q. Complete work is about

  1.2533·√q · c(δ) / √(2δ(1−δ)),

plus trail, restart and null charges. A fixed-difference fill is admissible only if it beats 0.886·(5M+S)·√q under that law, which requires c ≤ 3.0 at S/M=1. No current kernel meets this.

**Recommendation:** close Cards 1–3 on paper. Keep the H023 pair as a component only.

## 6. Frozen protocol, only if someone disputes the indegree law

This would be a diagnostic, not a solver race.

- **Curves.** Five ordinary curves of prime order q ∈ [2^22, 2^23] with p ≡ 3 mod 4 and j ∉ {0, 1728}, generated from a seed list fixed in advance.
- **Storage.** Use exact full-pair storage, which is acceptable for a diagnostic. This isolates the collision law from distinguished-point overhead.
- **Runs.** 200 seed-frozen runs per walk:
  - Card 1 at δ = 1/32;
  - Card 1 at δ = 1/4;
  - control (a): a 32-adding walk without negation;
  - control (b): a BLS-style negation 32-adding walk with 2-cycle escape, to calibrate 1.29 and about 0.89.
- **Bucket.** The integer representative of x mod 32. No retuning.
- **Measure.** Steps to the first non-null full-pair merge. Null merges trigger a restart and are counted.
- **Kill rule.** Mean steps/√q for Card 1 at δ = 1/32 ≥ 1.007, the break-even against rho, kills it. The predicted value is about 5.1.
- **Falsifies the law.** A mean outside [0.5×, 2×] of 5.09.
