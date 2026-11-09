# crown-vnumber-formal-pi-r4 SUMMARY

Status: **IN PROGRESS / PARTIAL** — no literal full endpoint yet. credit 0.
MathDB 369163. Accepted 52/60 campaign-wide (root bookkeeping); this lane claims nothing.

## What is proven (kernel-checked, strict `-DwarningAsError=true`, exit 0)

Six modules, in dependency order (all receipts in `receipt/`, full logs in `logs/`):

| module | src sha256 (prefix) | exit | note |
|---|---|---|---|
| CrownVGraph | 8e5e3195bd7c72a1 | 0 | vertices/cadj/SameC API (unchanged from r3) |
| CrownVCount | bd236fddbb423b03 | 0 | ccnt upper/lower bounds (unchanged) |
| CrownVSide  | cfcaf195fa7dd34e | 0 | swap/closure/connectivity API (unchanged) |
| CrownVAlg   | 01e65104c89fd9b3 | 0 | PolyRing/J/Pc/elcolon/homog/VIs defs (unchanged) |
| CrownVCut   | b475fd55b46b6cad | 0 | r4 repair; see CHECKPOINT; no `sorry` in code |
| CrownVClass | ed0204e2b5192007 | 0 | NEW: path head-decomposition, `VCut`, `Cutset` (paper Def 2.2) |

CrownVCut content now includes: the six-family index `Fam`, `famCut`/`FamPrime`
with `rfl`-unfold lemmas, killed-endpoint minor lemmas, mixKeep
(non)membership, and `minor_mem_FamPrime` — the inclusion `J ⊆ P_τ` for all six
family primes, with the three r3 `sorry` cases (mixed family) fully proved.

## Frozen inputs
313/313 sha256 verified BEFORE any mathematical read and AGAIN after work.
Do not overwrite `bootstrap-receipt.json`.

## Runner
`scripts/run.sh` + `check.sh` (r3 design): true exit propagation, CPU 120 s
ulimit, wall 140 s kill+reap of the process group, AS 12 GiB, affinity first 2
CPUs of the actual mask (0,1 here), sampled group-RSS guard 6 GiB (recorded as
sampled, not cgroup), `MALLOC_ARENA_MAX=2`, TMPDIR/cache in-lane. Signature
probes were run capped through the same runner (receipts 1793951613399345078,
1793953332308942719, 1793953341647445094, 1793953351312135364).

## What is NOT done (remaining bridges, in order)
1. Classification `Cutset T → ∃ f, famCut n f = T` (paper Thm 2.4 / [3, Thm 3.3]):
   path-crossing extraction from `VCut`, then case bash on survivor index sets.
   Answer: (A,B) ∈ {(∅,all),(all,∅),({i},all),(all,{i}),({i,j},{i,j})}, plus T=∅.
2. Exact-separator lemma (paper 3.1) — needs the irredundant six-family
   decomposition of J (radicality) or a genuinely equivalent direct colon route.
3. Multihomogeneous components + retraction/contraction (paper 4.1, 4.2).
4. Degree ≤ 3 exclusion per family, every field, char 2 included (5.1, 5.2,
   6.1, 6.2, 7.1, 7.2).
5. Quartic exact-colon witnesses for every family (section 8), exact at every
   actual `P_T`, all fields.
6. Assembly `VIs (Pc T) 4` for every `Cutset T` via 1; endpoint audits
   (module-origin declaration/body/axiom, only propext/Classical.choice/
   Quot.sound), negative controls, leanchecker, fresh source-only extract
   strict rebuild.

No FULL certificate, replay, or audit is claimed. Known ordinary theorems from
the source are treated as unproven obligations, not Lean axioms.
