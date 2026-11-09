from pathlib import Path
import runpy,json,re,hashlib
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4')
runpy.run_path(str(R/'report.py'),run_name='__main__')
p=R/'results.json';d=json.loads(p.read_text());assert d['fresh_compile_passes']==d['fresh_checker_passes']==d['module_count']==443
assert d['normalized_progress']['replayed_steps']==12500
assert d['metadata_audit'] and all('sorryAx' not in x for x in d['endpoint_axiom_output'])
rows=json.loads((R/'module-times.json').read_text());norm=[r for r in rows if r['module'].startswith('NReplay')]
d.update(status='conditional',endpoint='Percolation.NReplay.not_conjecture20_normalized_after12500',endpoint_statement='Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20',remaining_hypothesis='¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧ (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)',remaining_normalized_additions=117171,next_retained_step_one_based=12501,next_step_index_zero_based=12500,next_lrat_id=35873,last_verified_lrat_id=35872,normalized_input_theorems=11294,kernel_checked_collineations=86,NoMinimalTwoRound5='not proved',not_conjecture20_unconditional='not proved',normalized_replay_compile_seconds=round(sum(r['build']['wall_seconds'] for r in norm),2),normalized_replay_checker_seconds=round(sum(r['check']['wall_seconds'] for r in norm),2),fresh_run_description='Fresh extraction, resumed after one direct-clause elaboration correction. All final module source bytes compiled and checked with matching rolling dependency stamps. A later 500-addition module hit the CPU cap; its unverified source and all later replay modules are excluded from the final source archive.',source_scan={'files':443,'findings':[]},metadata_local_declarations=57890,unverified_generated_sources='unreplayed-generated/src/; excluded from source-only.zip',resource_failure={'module':'NReplay024','attempted_zero_based_steps':[12500,12499],'counted_as_replayed':0,'exit':137,'fixed_cpu_seconds_limit':120,'wall_seconds':111.28,'user_cpu_seconds':118.48,'system_cpu_seconds':2.28,'peak_sampled_rss_kib':2185064,'log':'fresh-extracted/logs/build-NReplay024.log'},retained_fresh_elaboration_failure='fresh-extracted/logs/build-NInputs206.failed-first.log',source_manifest_check='source-manifest-check.log; all 443 hashes passed')
p.write_text(json.dumps(d,indent=2))
summary=f'''# Round 4: normalization closed; 12,500 normalized additions checked

Endpoint: `Percolation.NReplay.not_conjecture20_normalized_after12500 : Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20`.

Status: conditional. Neither `NoMinimalTwoRound5` nor `not_conjecture20_unconditional` is proved. No acceptance, novelty, or campaign credit is claimed; root alone decides.

The exactly one remaining hypothesis is:

```lean
¬ ∃ v : SatVar → Bool,
  (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
  (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)
```

`prefix024` is exactly the first 12,500 retained additions of the normalized trimmed certificate. The last checked LRAT ID is **35872**. Continue at **zero-based steps[12500]**, retained addition **12501**, LRAT ID **35873**. Exactly **117,171** additions remain. The hypothesis is a frontier-refutation Prop, not a claim that those additions were replayed.

Normalization is fully kernel checked: arbitrary incidence-preserving point/line bijections of PG5 preserve step, every natural round, percolation, TimeIs, and Minimal. Every threshold-5 percolating infection contains a noncollinear triple. An explicit family of 86 checked collineations transports such a triple to 0, 25, 30. The transported witness satisfies the unchanged CNF and the three positive units. Lean's normalized export matches normalized.cnf byte for byte, including clause order and variable numbering.

The packet retains all 92 inherited Lean source modules byte-identically. It adds all 11,294 selected input-clause proofs needed by the complete normalized certificate, plus 25 chained modules of 500 verified normalized additions each. Later generated sources are clearly labeled unverified under unreplayed-generated/, outside the source archive.

Fresh extracted, strict, resumable verification passed for **443/443 compiler calls** and **443/443 explicit-module kernel checks** for the final packet. Compiler wall total: **{d['compile_wall_seconds']:.2f} s**. Checker wall total: **{d['checker_wall_seconds']:.2f} s**. Combined successful verification: **{d['combined_wall_seconds']:.2f} s**. The 12,500 normalized additions alone took {d['normalized_replay_compile_seconds']:.2f} compiler seconds and {d['normalized_replay_checker_seconds']:.2f} checker seconds. Per-module measurements are in module-times.json. The final 443-file source scan and metadata audit of 59,000 declarations passed; all 443 final source hashes passed. The endpoint's transitive axioms are only propext, Classical.choice, Quot.sound.

Replay was resumed after correcting a direct-clause simplification proof in NInputs206; the failure log is retained. The next replay module, NReplay024, hit the fixed 120 CPU-second limit (111.28 wall seconds, 2,185,064 KiB sampled RSS). None of its additions is counted. No resource limit was raised. This measured bottleneck is the immediate continuation issue: factor the expensive checks across helper modules or otherwise reduce their cost while keeping the fixed caps.

An earlier combined finite geometry check hit the RSS watchdog and was replaced by the argument from the plane axioms. Some initial development log labels were reused; available failures and the exact observed watchdog receipt are disclosed in results.json. All final fresh compiler/checker logs are retained. No lane-started job remains at handback.

Files: source-only.zip; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; normalized-progress.json; certificate-sha256.txt and .json; generator-correspondence.json; inherited-source-comparison.json; source-manifest-check.log; fresh-replay.log; fresh-extracted/logs/; packet/src/; and unreplayed-generated/README.md.

Source archive SHA256: `{d['source_zip_sha256']}`.
'''
(R/'SUMMARY.md').write_text(summary)
(R/'failure-history.json').write_text(json.dumps({'geometry_rss_failure':d['development_failures'][0],'normalized_replay_cpu_failure':d['resource_failure'],'fresh_elaboration_failure':d['retained_fresh_elaboration_failure']},indent=2))
print(json.dumps({k:d[k] for k in ['status','endpoint','module_count','compile_wall_seconds','checker_wall_seconds','combined_wall_seconds','normalized_replay_compile_seconds','normalized_replay_checker_seconds','source_zip_sha256']},indent=2))
