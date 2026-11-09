from pathlib import Path
import runpy,json,re
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');F=R/'fresh-extracted'
runpy.run_path(str(R/'report.py'),run_name='__main__')
d=json.loads((R/'results.json').read_text());g=d['normalized_progress'];assert g['replayed_steps']==12500
assert d['fresh_compile_passes']==d['fresh_checker_passes']==d['module_count']==443
assert d['metadata_audit'] and all('sorryAx' not in x for x in d['endpoint_axiom_output'])
metadata=int(re.search(r'passed: (\d+) declarations',d['metadata_audit'][0])[1])
rows=json.loads((R/'module-times.json').read_text());norm=[x for x in rows if x['module'].startswith(('NReplay','NDefs','NCheck'))]
c=sum(x['build']['wall_seconds'] for x in norm);k=sum(x['check']['wall_seconds'] for x in norm)
failed=json.loads((R/'checkpoint-12000/results.json').read_text())['resource_failure'];failed['module']='original unfactored NReplay024';failed['subsequently_closed_by_factored_replacement']=True;failed['log']='Receipt retained in fresh-replay.log and checkpoint-12000/results.json; original compiler log name was reused for the successful factored replacement.'
d.update(status='conditional',endpoint='Percolation.NReplay.not_conjecture20_normalized_after12500',endpoint_statement='Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20',remaining_hypothesis='¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧ (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)',remaining_normalized_additions=117171,next_retained_step_one_based=12501,next_step_index_zero_based=12500,next_lrat_id=g['next_lrat_id'],last_verified_lrat_id=g['last_lrat_id'],normalized_input_theorems=11294,kernel_checked_collineations=86,NoMinimalTwoRound5='not proved',not_conjecture20_unconditional='not proved',normalized_replay_compile_seconds=round(c,2),normalized_replay_checker_seconds=round(k,2),fresh_run_description='Fresh extraction resumed after a direct-clause proof correction and a factored replacement for a CPU-limited module. Every final module source byte was compiled and checked, with matching rolling dependency stamps. Unverified suffix drafts are excluded from the archive.',metadata_local_declarations=metadata,source_scan={'files':443,'findings':[]},unverified_generated_sources='unreplayed-generated/src/; excluded from source-only.zip. Original raw NReplay024 was replaced by the verified factored module; genuine remaining suffix starts at NReplay025.',resource_failure=failed,retained_fresh_elaboration_failure='fresh-extracted/logs/build-NInputs206.failed-first.log',source_manifest_check='source-manifest-check.log; all 443 hashes passed')
(R/'results.json').write_text(json.dumps(d,indent=2));(R/'normalized-progress.json').write_text(json.dumps(g,indent=2))
summary=f'''# Round 4: normalization closed; 12,500 normalized additions checked

Endpoint: `Percolation.NReplay.not_conjecture20_normalized_after12500 : Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20`.

Status: conditional. `NoMinimalTwoRound5` and `not_conjecture20_unconditional` remain unproved. Root alone decides acceptance. No novelty or campaign credit is claimed.

Exactly one remaining hypothesis:

```lean
¬ ∃ v : SatVar → Bool,
  (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
  (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)
```

`prefix024` is exactly the first 12,500 retained additions of normalized-trimmed.json. Last checked LRAT ID: **{g['last_lrat_id']}**. Continue at **zero-based steps[12500]**, retained addition **12501**, LRAT ID **{g['next_lrat_id']}**. Exactly **117,171** additions remain. The frontier-refutation hypothesis is explicit; no formal replay of the remaining suffix is claimed.

Normalization is fully proved. Arbitrary incidence-preserving point/line bijections preserve step, every natural round, percolation, TimeIs and Minimal. Every percolating threshold-5 infection contains a noncollinear triple. A family of 86 kernel-checked collineations transports it to 0, 25, 30. The transported witness satisfies the unchanged CNF plus those three positive units. The complete Lean DIMACS export matches normalized.cnf byte for byte, including clause order and numbering.

All 92 inherited Lean source files remain byte-identical. All 11,294 input-clause theorems selected by the complete normalized certificate are checked. Twenty-five chained replay modules each close 500 additions. For NReplay024, six helper modules separate the literal definitions and finite RUP checks from the 500 soundness proofs. This resolves the original aggregate module's CPU-cap failure without increasing a limit. Unverified later source drafts and the unconditional endpoint draft are outside source-only.zip.

Final extracted, strict, resumable verification passed **443/443 compiler calls** and **443/443 explicit-module leanchecker calls**. Successful compiler wall total: **{d['compile_wall_seconds']:.2f} s**. Checker wall total: **{d['checker_wall_seconds']:.2f} s**. Combined successful verification: **{d['combined_wall_seconds']:.2f} s**. Normalized replay and its helpers took {c:.2f} compiler seconds and {k:.2f} checker seconds. module-times.json gives all measurements.

The final 443-file source scan, all 443 source hashes, and metadata audit of **{metadata:,}** local declarations passed. The endpoint's axioms are only propext, Classical.choice, Quot.sound. The source replay was resumed after the direct-clause simplification correction and helper factorization; earlier unchanged module bytes and their dependency stamps remain validated.

The original unfactored NReplay024 hit the fixed 120 CPU-second limit (111.28 wall seconds, 2,185,064 KiB sampled RSS). Its receipt remains in fresh-replay.log and checkpoint-12000/results.json; its compiler-log name was later reused by the verified replacement. An earlier combined finite geometry check hit the RSS watchdog and was replaced by an argument from the plane axioms. Some initial development labels were reused; available failures and exact observed failure receipts are disclosed in results.json. All final successful fresh logs are retained. No resource limit was raised and no lane-started job remains.

Files: source-only.zip; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; normalized-progress.json; certificate-sha256.txt and .json; generator-correspondence.json; inherited-source-comparison.json; source-manifest-check.log; fresh-replay.log; fresh-extracted/logs/; packet/src/; check-factoring/; and unreplayed-generated/README.md.

Archive SHA256: `{d['source_zip_sha256']}`.
'''
(R/'SUMMARY.md').write_text(summary)
(R/'failure-history.json').write_text(json.dumps({'geometry_rss_failure':d['development_failures'][0],'original_normalized_replay_cpu_failure':failed,'fresh_elaboration_failure':d['retained_fresh_elaboration_failure']},indent=2))
print(json.dumps({k:d[k] for k in ['status','endpoint','module_count','compile_wall_seconds','checker_wall_seconds','combined_wall_seconds','normalized_progress','metadata_local_declarations','source_zip_sha256']},indent=2))
