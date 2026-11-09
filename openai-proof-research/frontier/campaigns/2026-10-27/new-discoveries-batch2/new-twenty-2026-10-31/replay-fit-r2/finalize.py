from pathlib import Path
import hashlib,json,re,zipfile
L=Path(__file__).resolve().parent
mods=(L/'modules.txt').read_text().splitlines()
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for m in mods:
 vals=[]
 assert (L/'logs'/('fresh-strict-'+m+'.ok')).exists()
 for stage in ['build','check']:
  p=L/'logs'/('fresh-strict-'+m+'.'+stage+'.log')
  matches=re.findall(r'GUARD peak_kib=(\d+) elapsed=(\d+) status=(\d+) reason=(\w*)',p.read_text())
  rss,wall,status,reason=matches[-1];assert status=='0' and reason==''
  vals.append({'wall_s':int(wall),'peak_rss_kib':int(rss),'log':str(p.relative_to(L))})
 rows.append({'module':m,'build':vals[0],'check':vals[1]})
with zipfile.ZipFile(L/'330264-replay-fit-r2-source.zip') as z:
 for name in z.namelist():
  assert z.read(name)==(L/'source'/name).read_bytes()==(L/'fresh-strict'/name).read_bytes()
assert json.loads((L/'fresh-strict/forbidden-metadata.json').read_text())==[]
raw=json.loads((L/'fresh-strict/closure-raw.json').read_text())
maxwall=max(v[k]['wall_s'] for v in rows for k in ['build','check'])
maxrss=max(v[k]['peak_rss_kib'] for v in rows for k in ['build','check'])
receipt={'scope':'REPLAY-FIT ROUND 2; NOT acceptance; root decides','archive_sha256':sha((L/'330264-replay-fit-r2-source.zip').read_bytes()),'modules':rows,'statement_closure_members':len(raw['closure']),'metadata_declarations':len(raw['packetDeclarations']),'forbidden_metadata':[],'endpoint_axioms':['propext','Classical.choice','Quot.sound'],'max_wall_s':maxwall,'max_peak_rss_kib':maxrss,'boundary_violation':'See INCIDENT.md: three marker lines appended to round 1 diagnostic log before correction.'}
(L/'fresh-replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(L/'FRESH-TIMINGS.md').write_text('| Module | Build wall s | Build peak KiB | Checker wall s | Checker peak KiB |\n|---|---:|---:|---:|---:|\n'+''.join('| '+r['module']+' | '+str(r['build']['wall_s'])+' | '+str(r['build']['peak_rss_kib'])+' | '+str(r['check']['wall_s'])+' | '+str(r['check']['peak_rss_kib'])+' |\n' for r in rows))
(L/'RESULT.md').write_text(f'''# Replay-fit round 2 handback: technical replay passed

Not acceptance. Credit is zero; root decides. The boundary violation below prevents a claim of fully instruction-clean execution.

MathDB 330264 only. Frozen input archive SHA-256 2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab and all recorded manifest file hashes were verified before restructuring. The corrected diagnostic of the original SpectralWitness reached the 140-second wall cap during A_intertwine, peak 2,822,968 KiB.

SpectralWitness is split into data, five-row certificate, identity-assembly and topology modules. All 34 original named declaration headers remain identical; matrix/data/topology declarations retain their original logical content. Nine matrix proofs now assemble separately checked row lemmas. The endpoint module, including its name, statement and proof, remains entirely byte-identical.

The Lean metaprogram computes a 10-member statement closure from the newly compiled endpoint because the original unsplit module cannot compile within the cap. It traverses types and bodies, including theorem/opaque bodies, for each packet constant reachable from the endpoint type. It excludes the endpoint proof as a traversal seed, as required. The complete closure lies in GroupSemantics and Endpoint, both entirely byte-identical. The source-span comparison checks every member against the original bytes; three generated matrix proof helpers inherit their parent declaration's source span. Every changed/moved declaration is mechanically checked outside the closure. See statement-closure.json and PRESERVATION.md.

The local metadata audit exposed six compiler-generated partial _unsafe_rec declarations in the original prerequisites. Explicit noncomputable modifiers on those six recursive definitions, plus noncomputable sections in NormalForm, TraceAction, AutomatonSemantics and MachineInvariant, suppress their generation. Their logical types and bodies are unchanged. preservation.py verifies that removing exactly these code-generation annotations restores the four original module files. All affected declarations are outside the closure.

Fresh strict replay extracted the source-only archive into fresh-strict with no objects. All {len(mods)} modules were built with Lean 4.34.1, -j2 -M3500 -DwarningAsError=true, one module per process, and passed explicit-module leanchecker. Every invocation used two CPUs, CPU 120 seconds, wall 140 seconds, 6 GiB process-group RSS and MALLOC_ARENA_MAX=2. Maximum sampled RSS was {maxrss:,} KiB and maximum wall time per call was {maxwall} seconds. No cap was raised. The audit checked {len(raw['packetDeclarations'])} packet declarations with zero forbidden unsafe/partial/implemented_by/extern/_unsafe_rec metadata. Endpoint axioms are exactly propext, Classical.choice and Quot.sound. Imported pinned mathlib/core objects remain trusted.

The source-only ZIP, packet.sha256, fresh-replay-receipt.json, FRESH-TIMINGS.md, all logs, statement-closure.json, PRESERVATION.md and REPRODUCE.md provide the reviewable packet and resumable replay. Development used some previously built objects; only fresh-strict records are fresh replay evidence. Earlier failed metadata and import-order diagnostics remain recorded separately; the fresh replay has no failed call.

## Boundary violation

The first copied diagnostic retained an absolute round 1 marker-log path and appended three diagnostic marker lines there before being stopped. This violated the lane-only write instruction. No mathematical source or object outside this lane was modified, and the old log was not restored because that would require another out-of-lane write. The corrected diagnostic and all subsequent work used lane-local paths. INCIDENT.md records the exact three lines and canceled call. Root must account for this violation separately from the technical replay result.

No git, child agents, network, browser, external messages, uploads, publication or ledger changes were used. Process inspection at handback is recorded in process-check.txt. No acceptance or novelty adjudication is claimed.
''')
print('fresh modules',len(mods),'max wall',maxwall,'max RSS KiB',maxrss)
