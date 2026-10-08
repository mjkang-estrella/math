# W015: tight cyclic signed-block coverage and an unused-cap limitation

Date: 2026-10-07. Status: independently verified arithmetic/finite-check result; no speedup.

## Hypothesis and scope

For q,m>0, let r=m−1 and s=2m−1. Sequential block i covers residues
is±j modulo q for 0≤j<m. The tight number of centers is ceil(q/s), expressed
as (q−1)/s+1. The old safe cap (q−1+r)/s+1 is equal or one larger.
The proposed exact first-match index for canonical d<q is zero when d≤r or
d+r≥q, and floor((d+r)/s) otherwise. These are arithmetic statements for this
particular signed construction, not a new algorithm or a general DLP lower bound.
They refine the known negation-map direction already sourced/reviewed in W006;
no additional primary-literature novelty claim is made.

Potential falsifiers: failure of coverage at a wrapped tail, an earlier match
than the formula, more than one extra old block, or complete sequential coverage
with fewer centers than the alleged tight cap. Cases q=1, m=1 and m>q must be
included. Coverage/minimal-index facts do not grant unique signed table digits;
existing stronger span/representation obligations remain separate.

## Distinct implementation and verification roles

Native Sol `/root/small_curve` owns only Research/SignedTight.lean, importing
unchanged SignedCoverage. It reports a compiled generic first-hit/coverage proof
without strictspan; final freeze and independent coordinator review pending.
Coordinator independently wrote scripts/signed_coverage_checks.py, constructing
all signed residue sets and earliest matches by explicit enumeration, without
using the proposed formula to construct those matches. Sol will independently
review this separate script/data after freezing its math source.

## Finite test evidence

Exact command (exit 0):
`timeout 60 python3 scripts/signed_coverage_checks.py > research/findings/W015-coverage-results.json`.

All q=1..64, m=1..32, every residue d=0..q−1: 2,048 parameter pairs,
66,560 scalar cases and 108,132 explicit signed-residue insertions. The script
asserts a one-million-insertion guard. No sampling, narrowed secret ranges or
random seed is used. All formula checks, coverage checks and minimal sequential
cap witnesses passed. Old cap equals tight in 1,224 pairs and is one larger in
824. Results are archived in W015-coverage-results.json.

## Negative performance implication

A smaller cap alone does not save actual work in an ideal early-stopping
matching search: every first match already occurs before that cap. It sharpens
a worst-case loop bound; the unused iterations of the old safe cap were never
executed on covered inputs. This is not an experiment claiming changed curve
runtime. The W006/W012 coordinate engine and archived measurements are untouched.
Any executable-group transfer still needs a matching/refinement theorem and
its preparation, canonicalization, group, memory and scalar costs. No new
speedup, calibrated time, exponent gain or whole-cost result follows.

## Outstanding work

Freeze/review all generic Lean statements and their assumptions; independently
review/reproduce the script; audit every claimed theorem; record proof failures,
run the integrated check and commit the coherent result. Research continues to
complete raw-input execution semantics and meaningful executable cost comparisons.


## Frozen generic proof and independent review

Sol's frozen source SHA-256:
`c04649a830d9b921e37f674f492f40a94718c2c53583fbf0634ee591ba6adf1e`.
Coordinator read every definition/proof and independently ran
`timeout 60 ./scripts/lake.sh env lean Research/SignedTight.lean`, followed by
an `./scripts/lake.sh env lean --stdin` recompilation with all 16 public axiom
reports appended (60-second bound). All passed with only propext/Quot.sound;
boundary_checks has no axioms. The first-hit/minimal-cap proofs quantify over
all q,m>0 and d<q, including m>q; no global strictspan assumption is needed.
Interior cases themselves exclude wraparound of earlier matches. A last-block
witness establishes minimality only among sequential centers 0,s,2s,... .
No proof of a general algorithm lower bound is asserted.

Generic claims include firstHit_exact, last_block_witness,
sequential_cap_minimal, sequential_coverage_iff, coverage and old-cap comparison.
All 16 public theorems are included in Audit.lean. Author's two intermediate
compile failures involved a division-lemma argument name/positivity automation,
then unavailable by_contra tactic; corrected. A later deprecation warning was
removed before the frozen clean compile. Independent review found no blocker.

Sol independently reviewed and reran the coordinator's disjoint Python script;
its JSON exactly matches the archived counts. No review failures, source edits
or differing experimental result. This completes the separated math-author /
experiment-author cross-review for this limited milestone.


Integrated validation: `./scripts/check.sh` exited 0 with 227 named theorem
dependency audits and the compiled demo. WordRun is an unintegrated work file;
its presence in the lexical screen is not proof acceptance. `git diff --check`
passed. Staging excludes the runner and its draft executable checks.
