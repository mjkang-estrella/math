from pathlib import Path
import json
r=Path(__file__).resolve().parent;d=json.loads((r/'results.json').read_text());f=d['fresh_replay'];p=d['replay_pilot'];info=d['prefix']
s=f'''# Round 3: verified RUP prefix; conditional endpoint

Endpoint: `Percolation.Replay.not_conjecture20_after2000 :
Percolation.Replay.ReplayFrontierUnsat5 → ¬ Percolation.Conjecture20`.

Status: conditional, not accepted. `NoMinimalTwoRound5` and the unconditional
endpoint are still unproved. No novelty or campaign credit is claimed.

Exactly one explicit remaining Prop:

```lean
Percolation.Replay.ReplayFrontierUnsat5 :=
  ¬ ∃ v : Percolation.SatVar → Bool,
    (∀ c ∈ Percolation.inputCNF5, Percolation.CNF.Holds v c) ∧
    (∀ c ∈ Percolation.Replay.prefix2000,
      Percolation.CNF.Holds (v ∘ Percolation.decodeVar) c)
```

`prefix2000` is the exact first 2000 retained additions of input-trimmed.json.
The last proved original LRAT ID is {info['last_id']}. Continue at retained
addition 2001 (zero-based steps[2000]); {info['remaining_additions']:,} additions
remain. This is a precise frontier-refutation Prop, not a claim that the suffix
is already formally encoded or replayed.

Closed pieces: a general kernel-checked RUP soundness theorem; selected input-clause
membership in the actual round-2 CNF; {info['used_input_count']} named input-clause theorems;
and 2000 distinct derived additions. The independent 500-step pilot repeats the
first 500 additions and is not extra progress. All inherited source files are
byte-identical, including Audit.lean; a separate AuditR3.lean extends the audit.

The exact Lean formula exports to 14,695 clauses over 1,085 variables. The
independent Python export is byte-identical to Lean #eval data output. Both
solver runs returned UNSAT: 5 seconds normalized, 67 seconds unnormalized.
Backward trimming plus independent RUP checking retained 129,671 normalized
additions and 1,285,481 unnormalized additions. The pilot uses the latter, so
there is no symmetry or normalization hypothesis. The normalized run remains
external evidence only.

Measured final recursor pilot:

| Additions | Compiler seconds | Compiler additions/s | Checker seconds | Checker additions/s |
| --- | --- | --- | --- | --- |
| 500 | {p['500']['build']['wall_seconds']:.2f} | {p['500']['build']['additions_per_second']:.2f} | {p['500']['check']['wall_seconds']:.2f} | {p['500']['check']['additions_per_second']:.2f} |
| 2000 | {p['2000']['build']['wall_seconds']:.2f} | {p['2000']['build']['additions_per_second']:.2f} | {p['2000']['check']['wall_seconds']:.2f} | {p['2000']['check']['additions_per_second']:.2f} |

These measurements were recorded in results.json before packaging or scaling.
The 2000-step pilot's sampled compiler peak RSS was
{p['2000']['build']['peak_group_rss_kib']:,} KiB. For future longer-hint steps,
500–1000 additions per module provides more margin than the 2000-step pilot.
At the measured compiler rate, the full unnormalized trace would take roughly
10.5 hours excluding input proofs, checks and possible harder later steps.
That is an estimate, not a measured full-certificate replay. This round therefore
hands back the explicitly conditional prefix rather than claiming completion.

Fresh extracted replay: {f['compiled']}/{d['module_count']} strict compiler passes and
{f['checked']}/{d['module_count']} explicit-module leanchecker passes. Compiler wall total
{f['build_wall_seconds']:.2f} s; checker wall total {f['check_wall_seconds']:.2f} s;
longest invocation {f['longest_wall_seconds']:.2f} s; maximum sampled group RSS
{f['peak_group_rss_kib']:,} KiB. The {d['module_count']}-file source scan has no findings.
Metadata: {d['metadata_audit']}. Endpoint axioms: only propext, Classical.choice,
Quot.sound. No resource limit was raised and no lane-started job remains.

The first recursive implementation generated a forbidden compiler helper and
was rejected by the audit. The delivered implementation uses an explicit,
noncomputable List.rec definition and passes the audit. Earlier rejected audit
and benchmark logs are preserved under logs/*before-recursor*. Some routine
elaboration retries reused log names; full final-development and fresh-replay
logs are retained. No failed elaboration is reported as a proved theorem.

Files: source-only.zip, results.json, module-times.json, PROOF.md,
STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, certificate-sha256.txt, provenance.json,
packet/src/, logs/, and fresh-extracted/logs/.
Archive SHA256: {d['source_zip_sha256']}.
Root alone decides acceptance.
'''
(r/'SUMMARY.md').write_text(s)
print(s)
