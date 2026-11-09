from pathlib import Path
import json,hashlib,zipfile,shutil,sys
r=Path(__file__).resolve().parent;p=r/'packet';ep=json.loads((r/'endpoint.json').read_text());res=json.loads((r/'results.json').read_text());e=ep['closed_additions'];uncond=e==129671
res.update(ep);res['status']='unconditional' if uncond else 'partial';res['unconditional_targets']='proved' if uncond else 'not proved';res['metadata_audit']='passed';res['source_scan']='passed';res['resource_incidents']=(r/'incident.txt').read_text();(r/'results.json').write_text(json.dumps(res,indent=2))
order=(r/'module-order.txt').read_text().splitlines();keep={m+'.lean' for m in order}
# Undelivered generated suffix sources are kept in development, never in source-only.zip.
for f in (p/'src').glob('*.lean'):
 if f.name not in keep:
  dest=r/'undelivered';dest.mkdir(exist_ok=True);shutil.move(str(f),dest/f.name)
comparison={}
with zipfile.ZipFile(r/'r7-source.zip') as z:
 for n in z.namelist():
  if n.endswith('.lean'):
   h=hashlib.sha256(z.read(n)).hexdigest();assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h;comparison[n]=h
(r/'retained-source-comparison.json').write_text(json.dumps(comparison,indent=2))
# Portable replay driver; same bounded commands and rolling source/output hash protocol.
t=(r/'replay-r8.sh').read_text().replace('cd "$R/fresh-extracted"','cd "$R"').replace('$R/fresh-extracted/build','$R/build').replace('$R/guard-r8.sh','$R/guard.sh')
(p/'replay.sh').write_text(t);shutil.copyfile(r/'guard-r8.sh',p/'guard.sh');shutil.copyfile(r/'scan-r8.py',p/'scan.py');shutil.copyfile(r/'module-order.txt',p/'module-order.txt')
f=res['fresh_replay'];windows=[v for v in json.loads((r/'optimized-scaling-measurements.json').read_text())['windows'] if v['start_index']==13561]
rate='; '.join(f"[{v['start_index']},{v['end_exclusive']}): {v['hints_per_second']:.3f} hint uses/s ({v['compiler_seconds']:.2f} s compile + {v['checker_seconds']:.2f} s check, peak RSS {v['peak_rss_kib']} KiB)" for v in windows)
status='Unconditional: the empty clause, normalized unsatisfiability and NoMinimalTwoRound5 are proved.' if uncond else f"Conditional on exactly RemainingSuffixUnsatR8: no valuation satisfies normalizedCNF5 together with the final proved clause, mask {tuple(ep['last_mask'])}. The actual unreplayed suffix is zero-based additions [{e},129671), {129671-e} additions."
summary=f'''# Round 8 implementation report

Endpoint: `{ep['endpoint']} : {ep['statement']}`.

{status}

Closed mask additions: [0,{e}). Preserved all 303 round 7 Lean modules byte-identically, verified against the pinned archive. New input proofs are in additional modules. Heavy split boundaries are exactly 13561, 14561 and 18561. The historical list frontier in inherited.zip is preserved separately and is never added to the mask frontier.

Measured full named-dependency heavy windows, charging new input proofs and both checks: {rate}. These overlapping windows are not added together. Named-chain-only and cumulative prefix times are separately reported in results.json. Measurements were recorded before generating the later suffix. Both incremental heavy-window rates exceeded 300 hints/s.

Replay: {f['modules']}/{len(order)} module compiler passes and explicit-module checker passes; compiler {f['compiler_seconds']:.2f} s, checker {f['checker_seconds']:.2f} s, combined {f['total_seconds']:.2f} s; peak RSS {f['peak_rss_kib']} KiB. Times are successful GNU process wall times, excluding watchdog/driver overhead and development failures. See results.json for the exact replay-tree construction.

Local metadata audit includes every delivered proof module and the expression builder. Source scan passes. Printed endpoint axioms are only propext, Classical.choice and Quot.sound. No acceptance claim; credit remains zero and root decides.

Development incidents: brief overlapping replay chunks were stopped, affected stamps invalidated and modules replayed; exclusive locking added. Expanded input proof indentation was corrected after one module failed. Full records are in incident.txt and logs/development. No limit was raised. An earlier unshared-mask version stopped at R8Chain106561 on the fixed -M3500 import-memory limit. MaskChainBuildR8 replaces repeated literal masks with named reducible definitions; the delivered status above describes the subsequent checked version.

Files: source-only.zip, module-order.txt, module-times.json, results.json, progress.json, PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, NEXT.md, source-scan.json, retained-source-comparison.json, fresh-source-comparison.json, axioms.txt, metadata-audit.txt, full-logs.zip and lane-owned generators.
'''
proof='''# Proof construction

The inherited definitions, PG5 geometry, percolation dynamics, finite CNF generator and normalization bridge are unchanged. Only named input proofs and named mask-RUP consequences are extended. This lane performs implementation work and makes no new source-fidelity or novelty clearance claim.

Each numeric input clause is independently matched against the hash-pinned normalized DIMACS file. Its literal-list proof follows from the inherited gate or normalization lemmas. A kernel-checked reflexivity equality identifies its encoded mask; input_sound transports the proved literal semantics through encode_cnf. No input entailment is assumed.

For each addition the data preparer computes masks and successive propagation choices. MaskChainBuild and MaskChainBuildR8 assemble ordinary proof expressions. The round 8 command gives every used mask ID a shared reducible definition, reducing imported proof memory. Kernel-checked definitions bind each name to its actual literal mask; all check and entailment proofs still reduce and typecheck normally. A reflexivity proof requires kernel reduction of the actual MaskRUP.check. The builder supplies each hint with the actual earlier named clause theorem, using cons_hints and nil_hints to assemble membership hypotheses. MaskRUP.check_sound gives the new named entailment. The builder is included in the local declaration metadata audit.

Deleting clauses is unnecessary: retaining previously proved consequences is sound. No SAT solver or Python result is a proof oracle. Every delivered module is strictly compiled and separately checked by leanchecker with an explicit module argument.

'''+status+'\n\nThe endpoint uses the unchanged normalized_unsat_implies_noMinimal5 and not_conjecture20_normalized bridges. Only the three allowed foundational axioms occur.\n'
correspondence='''# Statement correspondence

MathDB 333709 concerns Conjecture 20 of Gerbner–Keszegh–Meszaros–Patkos–Vizer, arXiv:1608.00531v1, SIAM J. Discrete Math. 32(2) (2018), 864–881. The inherited Lean proposition is:

`∀ (q : Nat) (P : Plane q) (r : Nat), 4 ≤ r → r ≤ q → ∃ a, Minimal P r a ∧ TimeIs P r a 2`.

The unchanged geometric endpoint refutes this universal proposition by the projective plane PG5 and threshold 5. NoMinimalTwoRound5 is the negation of the existence of a minimal infection on PG5 taking exactly two rounds. The normalization bridge maps any such witness to a valuation satisfying every generated normalized clause.

Numeric literal x corresponds to (abs(x)-1, x<0), which holds when the valuation differs from the sign Boolean. decodeVar maps numeric indices to structured SatVar values. Every named mask entailment quantifies over structured valuations satisfying normalizedCNF5. The input correspondence and normalization proofs are inherited byte-identically; this lane does not re-audit upstream truth or claim novelty.

'''+f"Delivered endpoint: `{ep['endpoint']} : {ep['statement']}`.\n\n"+status+'\n'
repro='''# Strict reproduction

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. No network is used. Extract source-only.zip into a new directory inside this lane, rejecting absolute paths and parent components. Check `sha256sum -c source-manifest.sha256`.

Run `RESUME=1 BUDGET=55 bash replay.sh` repeatedly until every ordered module has passed. BUDGET is checked between modules; a started module may finish beyond the chunk budget. One compiler and one explicit-module leanchecker run serially per module. An exclusive flock prevents overlapping drivers. Successful stamps are skipped only if rolling source hashes and compiled-output hashes match. A failure stops replay.

Each process has affinity CPUs 0,1, CPU limit 120 s, wall limit 140 s, process-group RSS watchdog 6 GiB, MALLOC_ARENA_MAX=2 and local tmp/cache directories. Every Lean invocation uses -M3500 and -DwarningAsError=true. Never increase a limit after failure. Every Python call must likewise use guard.sh and a real script path, with python3 -I -B. For example: `bash guard.sh scan python3 -I -B scan.py "$PWD"`.

AuditR8 imports every delivered proof module and checks local metadata, including the expression builder, for local axioms, unsafety, partial definitions, extern bindings, compiler implementation substitutions and generated unsafe recursion helpers. EndpointR8 prints the endpoint axiom closure. Source scan strips strings and nested comments before checking executable forbidden tokens.

The archive is source only. Module times exclude failures, development and shell/watchdog overhead. Historical inherited.zip remains a separate byte-identical archive. Acceptance is for root to determine.
'''
nexttext=f'''# Continuation

{status}

Read results.json, progress.json and module-times.json. Only successful strict compiler-plus-checker stamps establish replay. The current checked frontier is {e}. Preserve all delivered Lean modules byte-identically. Continue named theorem dependencies and add any new inputs in additional modules. Keep the same process caps; never infer replay from generated source presence. Heavy measurements are now complete: {rate}.
'''
for name,txt in [('SUMMARY.md',summary),('PROOF.md',proof),('STATEMENT-CORRESPONDENCE.md',correspondence),('REPRODUCE.md',repro),('NEXT.md',nexttext)]:
 (r/name).write_text(txt);(p/name).write_text(txt)
for name in ['results.json','progress.json','module-times.json','retained-source-comparison.json','source-scan.json','incident.txt','scaling-measurements.json','optimized-scaling-measurements.json']:
 if (r/name).exists():shutil.copyfile(r/name,p/name)
manifest=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='source-manifest.sha256' and ('build' not in f.relative_to(p).parts):manifest.append(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+str(f.relative_to(p)))
(p/'source-manifest.sha256').write_text('\n'.join(manifest)+'\n')
with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED,compresslevel=1) as z:
 for f in sorted(p.rglob('*')):
  if f.is_file():assert f.suffix not in ['.olean','.ilean','.so'];z.write(f,str(f.relative_to(p)))
print('source-only.zip',hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest())
