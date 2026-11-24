# MathDB 361006, Lean stage 2 (root Claude Fable 5.2, 2026-11-23)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Wang, arXiv:2312.01633, Conjecture 1.6: the proper rational spherical triangles are exactly the two-right-side family and eight sporadic ones.

## Where things stand
- Proof (GPT-6.2 Sol, computer-assisted): `C/t1-pool224-proof-sol62-20261123-r1/PROOF-361006.md`, with scripts and logs.
- Adversarial review (Claude Opus 5.5, cleared, not-routine 0.75): `C/t1-prelean-X105-opus-20261123-r1/REVIEW-361006.md`, with its own independent scripts (conductor bound, torsion search).
- Lean stage 1 (GPT-6.2 Sol, PARTIAL): `C/rational-spherical-361006-formal-paper-sol62-20261123-r1`. Read its `REPORT.md` in full first (certificate design, what is checked, measurements, and the table "Remaining Lean work") and `MODULES.md`. It has 132 kernel-checked modules (24 hand-written, 2,876 lines; 108 generated, 21,573 lines). Checked so far: the statement `Wang.Conjecture16 : Prop` (for all rational E a b c, Omega2 E a b c iff Lambda1 E a b c or Lambda2 E a b c), the reverse implication `wang_conj_1_6_Omega2_reverse`, `affine_line_family`, `conductor_small_prime_exponents`, `conductor_dvd_of_small_primes` (which still assumes that only the primes 2, 3, 5, 7 divide the conductor), and `grid24_classification`. The one link outside Lean, accepted by root, is Wang's own Proposition 2.2 (Omega1 = Omega2).

What is missing for `theorem wang_conj_1_6_Omega2 : Wang.Conjecture16`:
- **Part P (prime support).** A theorem of exactly this type (the missing hypothesis of `conductor_dvd_of_small_primes`):
  ```lean
  theorem Wang.prime_support {t x y z : ℚ}
      (hproper : Proper ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi))
      (hzero : Laurent ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi) = 0)
      (hfamily : ¬ RightFamily ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi)) :
      ∀ p, (conductor t x y z).factorization p ≠ 0 → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7
  ```
  This is the first two rows of the stage-1 table: all primes at least 11 when the local groups vanish (determinant spectrum over four-element subsets of the 64 primitive directions, zero-partition exclusions at 11, 13, 17), and the case of local exponent exactly one (primes above 23 by fewer terms than the prime; 17, 19, 23 by the unit argument; 11 and 13 by interval and parity patterns). Stage-1 estimate 700 to 1,300 hand-written lines plus generated checks.
- **Part G (global search and assembly).** A theorem
  ```lean
  theorem Wang.wang_conj_1_6_Omega2_of_prime_support
      (hP : ∀ {t x y z : ℚ}, Proper ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi) →
            Laurent ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi) = 0 →
            ¬ RightFamily ((t : ℝ)*Real.pi) ((x : ℝ)*Real.pi) ((y : ℝ)*Real.pi) ((z : ℝ)*Real.pi) →
            ∀ p, (conductor t x y z).factorization p ≠ 0 → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) :
      Wang.Conjecture16
  ```
  that is, the last rows of the stage-1 table: the exact search over all conductors dividing 352,800 = 2^5 * 3^2 * 5^2 * 7^2 by a verified four-primary coefficient-elimination checker with coverage of every branch, the CRT orbit expansion and proper-domain checks, and the translation of the surviving tangent solutions into the literal Lambda1 and Lambda2 predicates, assembled with the reverse implication. Stage-1 estimate 980 to 1,850 hand-written lines plus generated checks.

Two lanes work in parallel, one per part. Your task message says which part is yours.

## How to work so that the two lanes can be merged
1. Read `C/public-claim-100/BRIEF-L-LEAN.md` for the Lean rules (specific imports only, never `import Mathlib`; only the axioms propext, Classical.choice, Quot.sound; no sorry, admit, axiom, unsafe or native_decide; the 32 GiB runner).
2. Create your lane folder (named in your task message) and copy the whole stage-1 folder contents into it. Write only in your lane folder.
3. **Do not edit any stage-1 module.** Add new modules only, with names starting with the prefix given in your task message. Do not introduce a shared definition for the prime-support statement: part P proves a theorem of exactly the type above, and part G takes exactly that statement as the hypothesis `hP`, so that the merge is one application. If you find that the statement above is wrong or unprovable as written (an implicit-argument issue, a missing side condition), state the corrected proposition, prove it (part P) or use it (part G), and report it at the top of your REPORT.md so that the merge lane can reconcile the two.
4. Generated certificate modules are allowed and may be large in total; keep each small enough for the runner, measure time and memory on one piece before generating the rest, keep the generator script and say how to rerun it. Certificates must be checked in the kernel by `decide` or kernel reduction on small pieces, not by native_decide. Completeness of a search must not depend on the generator: the checker must verify coverage (stage 1 did this with an explicitly checked mixed-radix index).
5. Run Lean only under `taskset -c <your cores>` (given in your task message), through the 32 GiB runner, never more than three Lean processes at once.
6. Do not stop at the first obstacle. If you cannot finish, deliver everything that compiles, with the unproved part reduced to the smallest precisely stated hypotheses (as explicit hypotheses of theorems, never axioms), and list exactly which lemmas and which ranges remain with an estimate for each.

## Deliverables (in your lane folder)
- `src/` with the stage-1 modules unchanged and your new modules; `LEAN-SOURCE-APPENDIX.md` for ALL modules in import order (stage 1 plus yours), byte-identical to `src/`, in the format of the brief; `REPORT.md` (what is proved, full Lean statements, axioms output, what remains, corrected statements as in point 3, generator instructions, time and memory of the heaviest modules); `result.json` `{"mathdb_id": 361006, "part": "P|G", "status": "COMPLETE|PARTIAL", "theorems": [...], "new_modules": [...], "remaining": [...], "corrected_hypotheses": [...], "notes": ...}`.
- Do not rewrite PAPER.md; the merge lane does that. If your part shows that the written proof needs a correction, put the corrected text in `PAPER-NOTES.md`.

## Rules
No git commands at all, not even read-only ones such as `git status`. Nothing submitted, published or sent anywhere. No subagents. Do not open mathdb.com. Python as `python3 -I -B` from inside your own folder (numpy is not available; use exact integer arithmetic). At most 3 cores. Do not end your turn with a computation still running.

Final message: status, the full Lean statement of each theorem you proved, new module names with line counts (hand-written and generated separately), the axioms output, what remains, and anything the merge lane or root must decide.
