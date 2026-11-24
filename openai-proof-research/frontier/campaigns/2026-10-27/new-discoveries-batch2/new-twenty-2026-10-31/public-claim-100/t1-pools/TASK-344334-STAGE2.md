# MathDB 344334, Lean stage 2 (root Claude Fable 5.2, 2026-11-23)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Hare and Jankauskas, arXiv:1910.13994, Conjecture 2.13: the only inadmissible pairs (k, n) for Littlewood polynomials are (2, n) and (n-2, n) for n >= 13 with n = 1 mod 6.

## Where things stand
- Proof (GPT-6.2 Sol, computer-assisted): `C/t1-pool223-proof-sol62-20261123-r1/PROOF-344334.md`, with `ATTEMPT-344334.md`, logs and `scripts/`.
- Adversarial review (Claude Opus 5.5, cleared, not-routine 0.85, one small repair to section 2): `C/t1-prelean-X109-opus-20261123-r1/REVIEW-344334.md`, with its own scripts.
- Lean stage 1 (GPT-6.2 Sol, PARTIAL): `C/littlewood-pairs-344334-formal-paper-sol62-20261123-r1`. Read its `REPORT.md` in full first: it gives the route decision, what is checked, and a table of the remaining lemmas with line estimates. It has 18 kernel-checked modules in `src/` (2,730 hand-written lines plus 243 generated). The final theorem `Littlewood.hare_jankauskas_2_13` in `LittlewoodEndpoint.lean` is proved from five source theorems taken as named hypotheses (Mukunda_2_6, HareJankauskas_2_7, _2_8, _2_9, _2_11; root accepts these as links outside Lean, because they are the source's own printed theorems) and from five OPEN hypotheses that must become Lean theorems:
  - `SchurCohnRootCount`, `ReciprocalCoprimeTwo` (part A)
  - `ForbiddenMatrixCertificate` (part B)
  - `EvenFamilyArcCount`, `EvenFamilyRadialCount` (part C)

Three lanes work in parallel, one per part. Your task message says which part is yours.

## How to work so that the three lanes can be merged
1. Read `C/public-claim-100/BRIEF-L-LEAN.md` for the Lean rules (specific imports only, never `import Mathlib`; only the axioms propext, Classical.choice, Quot.sound; no sorry, admit, axiom, unsafe or native_decide; the 32 GiB runner).
2. Create your lane folder (named in your task message) and copy the whole stage-1 folder contents into it (src/, runner scripts, PINS.json, scripts, evidence). Write only in your lane folder.
3. **Do not edit any stage-1 module.** Add new modules only, with names starting with the prefix given in your task message, importing the stage-1 modules they need. If you find that a stage-1 definition or hypothesis statement is wrong or unprovable as stated (for example a missing side condition), do not change it silently: state the corrected proposition in a new module, prove it, prove that it suffices for the endpoint (a variant of `hare_jankauskas_2_13` in your own module that uses the corrected hypothesis), and report this at the top of your REPORT.md so that the merge lane can adopt it.
4. Your deliverable is, for each of your hypotheses H, a kernel-checked `theorem <name> : H` (or the corrected version as in point 3). If your part needs another part's hypothesis (for example part C's base case uses the Schur-Cohn root count), take that hypothesis as an explicit argument of your theorem, with exactly the stage-1 statement; the merge lane will discharge it.
5. Generated certificate modules are allowed and may be large; keep each generated module small enough for the runner (stage 1 had to split a 60-case module into three shards of 20 because of the CPU budget). Measure time and memory on one piece before generating the rest. Keep the generator script and say how to rerun it. Certificates must be checked in the kernel by `decide` or kernel reduction on small pieces, not by native_decide.
6. Run Lean only under `taskset -c <your cores>` (given in your task message), through the 32 GiB runner, never more than three Lean processes at once.
7. Do not stop at the first obstacle. If you cannot finish, deliver everything that compiles, with the unproved part reduced to the smallest precisely stated hypotheses, and list exactly which lemmas remain with a line estimate for each.

## Deliverables (in your lane folder)
- `src/` with the stage-1 modules unchanged and your new modules; `LEAN-SOURCE-APPENDIX.md` for ALL modules in import order (stage 1 plus yours), byte-identical to `src/`, in the format of the brief; `REPORT.md` (what is proved, full Lean statements of your theorems, axioms output, what remains, anything changed as in point 3, generator instructions); `result.json` `{"mathdb_id": 344334, "part": "A|B|C", "status": "COMPLETE|PARTIAL", "theorems": [...], "new_modules": [...], "remaining": [...], "corrected_hypotheses": [...], "notes": ...}`.
- Do not rewrite PAPER.md; the merge lane does that. If your part shows that the written proof needs a correction, put the corrected text in `PAPER-NOTES.md`.

## Rules
No git commands at all. Nothing submitted, published or sent anywhere. No subagents. Do not open mathdb.com. Python as `python3 -I -B` from inside your own folder (numpy is not available; use exact integer arithmetic). At most 3 cores. Do not end your turn with a computation still running.

Final message: status, the full Lean statement of each theorem you proved, new module names with line counts (hand-written and generated separately), the axioms output, what remains, and anything the merge lane or root must decide.
