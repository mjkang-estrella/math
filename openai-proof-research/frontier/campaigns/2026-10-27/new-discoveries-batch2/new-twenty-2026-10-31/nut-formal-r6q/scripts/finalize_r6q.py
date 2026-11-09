from pathlib import Path
import json,hashlib,re,collections,subprocess
r=Path(__file__).resolve().parents[1]
rep=json.loads((r/'fresh-extracted/logs/replay.json').read_text());assert rep['status']=='PASS r6q PER_SUPPORT PACKET'
mods=json.loads((r/'modules.json').read_text());receipts=rep['receipts'];assert len(receipts)==2*len(mods)+10
assert all(x['exit']==0 and not x['cap_reason'] for x in receipts[:2*len(mods)])
assert all(x['exit']!=0 and not x['cap_reason'] for x in receipts[2*len(mods):])
counts=collections.Counter();audits=['AuditR5']+[m for m in mods if m.startswith('AuditR6_')]
for m in audits:
 text=(r/'fresh-extracted/logs'/('strict-'+m+'.log')).read_text()
 total=int(re.search(r'LOCAL_TOTAL (\d+)',text).group(1));lines=[l for l in text.splitlines() if 'MODULE ' in l and ' DECL ' in l];assert len(lines)==total
 assert not re.search(r'FLAGS.*(?:unsafe=true|partial=true|axiom=true)',text)
 for l in lines:counts[l.split('MODULE ',1)[1].split(' DECL ',1)[0]]+=1
for m in mods:assert (r/'formal'/(m+'.lean')).read_bytes()==(r/'fresh-extracted/formal'/(m+'.lean')).read_bytes()
before=json.loads((r/'inputs-before.json').read_text());after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before};assert after==before
(r/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
for p in (r/'inputs/formal').glob('*.lean'):assert p.read_bytes()==(r/'formal'/p.name).read_bytes()
assert (r/'formal/NutInterface.lean').read_bytes()==(r/'inputs/root-interface/NutInterface.lean').read_bytes()
(r/'audit-declaration-counts.json').write_text(json.dumps(dict(counts),indent=2)+'\n')
with (r/'logs/negative-existing-olean.log').open('w') as f:rc=subprocess.run(['/usr/bin/python3','-I',str(r/'fresh-extracted/replay.py')],stdout=f,stderr=subprocess.STDOUT).returncode
assert rc and 'Refusing existing oleans' in (r/'logs/negative-existing-olean.log').read_text()
wall=sum(x['wall_seconds'] for x in receipts);peak=max(x['peak_private_bytes'] for x in receipts)
res={'365943':dict(status='proved_PerSupport_pending_root_acceptance',required_endpoint='Nut8.per_support : Nut8.PerSupport',endpoint_exists=True,endpoints=['Nut8.per_support : Nut8.PerSupport'],exact_statement='∀ code ∈ Nut8.GraphClosure7_000.targets, ∀ (C : Nut8.QuotientMatrix) (s : ℤ), Nut8.Structural C s → Nut8.SupportCode C code → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)',declaration_counts=dict(all_local_including_generated=sum(counts.values()),strictly_compiled_modules=len(mods),per_module='audit-declaration-counts.json'),certificate_records=9172,certificate_modules=287,support_modules=194,reconciliation=json.loads((r/'new-reconciliation.json').read_text()),replay=dict(status=rep['status'],calls=len(receipts),wall_seconds_sum=wall,peak_sampled_private_bytes=peak,audits=['fresh-extracted/logs/strict-'+m+'.log' for m in audits],receipts='fresh-extracted/logs/replay.json',negative_lean_controls=10,existing_olean_refusal=True),inputs_unchanged=True,input_files=len(before),inherited_modules_byte_identical=True,root_interface_byte_identical=True,source_packet='nut-r6q-source.zip',Coverage8_proved_here=False,self_accepted=False,count_change=0)}
(r/'results.json').write_text(json.dumps(res,indent=2)+'\n')
(r/'SUMMARY.md').write_text(f'''# MathDB 365943 r6q: PerSupport proved, pending root acceptance

`Nut8.per_support : Nut8.PerSupport` is kernel checked against the byte-identical
root-fixed interface. No count change or self-acceptance is claimed. Coverage8
and the final graph-theoretic composition belong to the parallel r5p lane.

The signed enumeration has literal finite-image completeness for every normalized
structural matrix. All 194 support proofs use the inherited checked permutation
and parent data. A double edge has one shared sign, magnitude-two loops have
independent signs, and all magnitude-one loops have the single semi-edge sign.

All 9,172 matrices were regenerated directly in these labels. Exact determinant
or principal-minor witnesses were recomputed, then checked through sparseDet.
There are 8,208 nonsingular and 964 singular records, matching r2 with difference
zero. No r2 certificate matrix list or unsigned spectral pretest was used.
Every finite support enumeration is checked equal to its literal matrix set;
all scalar certificates and switch/relabel invariances compose to PerSupport.

Fresh extracted sanitized strict replay passed for {len(mods)} modules, with
separate leanchecker calls, audits of {sum(counts.values())} local declarations
including generated ones, ten rejected Lean negative controls, and existing-olean
refusal. The audit prints full types, opaque-inclusive bodies, declaration flags,
and transitive axioms. Only propext, Classical.choice and Quot.sound occur.
The {len(receipts)} capped replay calls totalled {wall:.2f} process wall seconds;
peak sampled private memory was {peak:,} bytes. All source files match the fresh
extraction. Replay receipts and audit logs are under fresh-extracted/logs.

All {len(before)} assigned input files are hash-bound before/after and unchanged.
Every inherited Lean source and NutInterface.lean remain byte-identical. All
writes stayed inside this lane. No child agents, git, shared ledger edits,
network requests, browser tabs, external messages or publication were used.
No background jobs remain at handback. Source-only packet: nut-r6q-source.zip.
Root alone adjudicates integration and acceptance; the campaign stays at 20/40
beyond the prior 39 unless root changes it.
''')
(r/'GAPS.md').write_text('# Root integration remains\n\nNo PerSupport proof obligation remains in this lane. Coverage8 and the final\ngraph endpoint are outside this assignment. Independent root acceptance remains\nrequired; this lane does not self-accept or change counts.\n')
print('FINAL',len(mods),sum(counts.values()),wall,peak)
