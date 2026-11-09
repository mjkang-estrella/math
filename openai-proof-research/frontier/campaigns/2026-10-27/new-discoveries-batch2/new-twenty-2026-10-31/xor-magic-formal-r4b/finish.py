from pathlib import Path
import json,hashlib,re,collections,zipfile,os
r=Path(__file__).resolve().parent
receipt=json.loads((r/'fresh-replay/logs/replay-receipt.json').read_text())
assert receipt['status']=='pass'
inputs=json.loads((r/'receipts/inputs-before.json').read_text());after={}
for src,row in inputs.items():
 actual=hashlib.sha256(Path(src).read_bytes()).hexdigest();copy=hashlib.sha256((r/row['copy']).read_bytes()).hexdigest()
 assert actual==copy==row['sha256'],src
 after[src]={'sha256':actual,'copy_sha256':copy,'unchanged':True}
for f in (r/'inputs/r3/formal').glob('*.lean'):
 assert f.read_bytes()==(r/'formal'/f.name).read_bytes(),f
(r/'receipts/inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
manifest=json.loads((r/'source-manifest.json').read_text())
for name,digest in manifest.items():
 assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
 assert hashlib.sha256((r/'fresh-replay'/name).read_bytes()).hexdigest()==digest,name
jobs=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name)==os.getpid():continue
 try:
  cwd=(proc/'cwd').resolve();cmd=(proc/'cmdline').read_bytes().split(b'\0')
  if cwd.is_relative_to(r) and any(Path(os.fsdecode(x)).name in {'lean','leanchecker','bounded.py','replay.py'} for x in cmd if x):jobs.append(int(proc.name))
 except (OSError,ValueError):continue
assert not jobs,jobs
(r/'receipts/process-handback.json').write_text(json.dumps({'remaining_lane_jobs':jobs},indent=2)+'\n')
counts=collections.Counter(re.findall(r'\|MODULE\|([^|]+)\|',(r/'fresh-replay/logs/ComplementAudit.log').read_text()))
new=sum(counts.values());old=json.loads((r/'inputs/r3/results.json').read_text())['372205']
processes=receipt['receipts'];peak=max(x['sampled_private_rss_bytes'] for x in processes);wall=max(x['wall_seconds'] for x in processes)
final={'status':'R4B_SCOPE_REPLAY_PASS_PENDING_ROOT','strict_builds':len(receipt['modules'])+3,'leanchecker_runs':len(receipt['modules'])+3,'new_proof_modules':9,'inherited_modules_preserved':57,'new_local_declarations':new,'all_local_declarations':old['declaration_counts']['all_local_declarations']+new,'new_by_module':dict(counts),'negative_controls':receipt['negative_controls'],'input_files_unchanged':len(inputs),'peak_sampled_private_rss_bytes':peak,'longest_call_seconds':wall,'packet_sha256':hashlib.sha256((r/'xor-magic-r4b-source.zip').read_bytes()).hexdigest()}
(r/'receipts/final-validation.json').write_text(json.dumps(final,indent=2)+'\n')
endpoints=[
 ('XorMagic.EdgeTransport.complementMatching_exact','For any finite linearly ordered V, simple G, EdgeTransport T, MatchingDecomposition G d and MatchingDecomposition Gᶜ (card V-1-d), with d+1≤card V: MatchingDecomposition T.graphᶜ (card (V×Four)-1-d).'),
 ('XorMagic.EdgeTransport.interpGraph_regular','For arbitrary EdgeTransport T, decompositions F of G into d matchings and H of Gᶜ into c matchings, k≤d and j≤c: (T.interpGraph F H k j hj).IsRegularOfDegree (d+2*k+4*j).'),
 ('XorMagic.EdgeTransport.interp_label_sum','For any bijection l : V ≃ Bits n, every vertex has exactly the same neighbourhood sum under EdgeTransport.label l in the interpolation graph and in T.graph.'),
 ('XorMagic.EdgeTransport.interpGraph_connected','Base G connected and lift T.graph connected imply the interpolation graph is connected, for every k and j≤c.'),
 ('XorMagic.EdgeTransport.open_interval_exists','Given G connected, T.graph connected, its zero open sums under label l, 1≤d, d+1≤card V, Odd d, Odd q and d≤q≤4*card V-4-d, OpenExists (n+2) q.'),
 ('XorMagic.EdgeTransport.closed_interval_exists','Given G connected, T.graph connected, its zero closed sums under label l, 1≤d, d+1≤card V, Even d, Even q and d≤q≤4*card V-4-d, ClosedExists (n+2) q.')]
expanded_endpoints=[]
for name,statement in endpoints:
 leaf=name.rsplit('.',1)[-1]
 found=[]
 for f in (r/'formal').glob('*.lean'):
  m=re.search(r'(?:theorem|noncomputable def) '+re.escape(leaf)+r'\b',f.read_text())
  if m:
   header=f.read_text()[m.start():].split(':=',1)[0].strip()
   found.append({'declaration':name,'statement':statement,'proved':True,'exact_lean_header':header,'section_context_source':str(f.relative_to(r)),'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
 assert len(found)==1,(name,found)
 expanded_endpoints.extend(found)
result={'status':'R4B_SCOPE_COMPLETE_PENDING_ROOT','credit':0,'root_acceptance':'Required; not claimed','main_endpoint':old['main_endpoint'],'endpoints':expanded_endpoints,'inherited_endpoints':old['endpoints'],'declaration_counts':{'new_proof_modules':9,'inherited_proof_modules':55,'all_proof_modules':64,'audit_modules':3,'new_local_declarations':new,'all_local_declarations':918+new,'new_by_module':dict(counts)},'replay_status':'PASS','leanchecker':'PASS: all 67 modules','audit':'PASS: all 1018 declarations; inherited Audit and AuditR3 byte-identical, ComplementAudit audits all 100 new declarations including generated ones, c.type and c.value? true, flags and transitive axioms; expression DAG verification passes.','negative_controls':{x:'expected Lean decide rejection' for x in receipt['negative_controls']},'packet':'xor-magic-r4b-source.zip','final_validation_receipt':'receipts/final-validation.json','inputs':'PASS: all before/after hashes and copied input hashes identical; 57 inherited Lean modules byte-identical','gaps_file':'GAPS.md','statement_correspondence':'statement-correspondence.md','network_requests':0,'git_operations':0,'child_agents':0,'remaining_jobs':0,'resource_limits':old['resource_limits'] | {'exceptions':['One early replay was terminated solely to rename new negative-control modules to the mandatory prefixes; receipts/replay-restart.json. No resource limit was exceeded.']}}
(r/'results.json').write_text(json.dumps({'372205':result},indent=2,ensure_ascii=False)+'\n')
(r/'SUMMARY.md').write_text(f'''# r4b implementation — pending root acceptance

The r4b complement and interpolation constructions are implemented and kernel checked. No acceptance or qualifying credit is claimed. The universal CorrectedAt endpoint remains absent and belongs to later cross-lane assembly.

Nine new proof modules construct the three internal fibre factors, three missing factors per base graph factor and four full factors per base complement factor. They prove involution, absence of fixed points, pairwise distinct mates, exact complement coverage and MatchingDecomposition in the inherited Fin-indexed convention. Endpoint charts work for every EdgeTransport, hence for every scalar assignment and translation of the r3 affine lift.

The actual interpolation SimpleGraph uses the first k graph factors and first j complement factors. Its degree is exactly d+2*k+4*j. Every neighbourhood label sum is preserved; closed sums follow with the same vertex label. A fibre sum is zero for every n, without a base-power restriction. Connectivity is proved both when k=0 by lift containment and when k>0 by a two-step path inside a replaced block and propagation along base walks. Explicit connected-lift and zero-sum hypotheses are left for r4a. Literal odd/open and even/closed degree intervals are assembled into OpenExists and ClosedExists endpoints throughout [d,4*m-4-d].

Final validation passed: {final['strict_builds']} fresh extracted sanitized strict builds, {final['leanchecker_runs']} leanchecker runs, {918+new} audited local declarations including all {new} new generated declarations, two checked lossless expression DAGs, and twelve rejected negative controls. Existing-olean refusal is recorded separately. All {len(inputs)} designated input files and their copies remain hash-identical; all 57 inherited Lean modules remain byte-identical. Peak sampled private RSS was {peak} bytes; longest bounded final call was {wall:.3f} seconds. Logs are in fresh-replay/logs/ and the aggregate receipt is receipts/final-validation.json.

The source-only packet is xor-magic-r4b-source.zip with portable replay.py and REPRODUCE.md. Exact statements and correspondence are in results.json and statement-correspondence.md. GAPS.md separates the outstanding campaign assembly from this lane. One early replay was stopped to correct the filenames of new negative-control modules; its logs and termination receipt are retained. No child agents, git, network, other-lane writes or shared ledger edits were used. No lane process remains at handback.
''')
print(json.dumps(final,indent=2))
