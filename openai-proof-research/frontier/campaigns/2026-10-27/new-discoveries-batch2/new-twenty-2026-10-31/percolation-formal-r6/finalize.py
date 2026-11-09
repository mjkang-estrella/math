import pathlib,json,hashlib,zipfile,shutil
r=pathlib.Path(__file__).resolve().parent;f=r/'fresh-extracted';p=r/'packet'
res=json.loads((r/'results.json').read_text());mods=(f/'module-order.txt').read_text().splitlines()
assert res['modules_verified']==len(mods)
for m in mods:
 assert (f/'src'/f'{m}.lean').read_bytes()==(p/'src'/f'{m}.lean').read_bytes()
 assert (f/'logs'/f'{m}.ok').exists()
scan=json.loads((f/'logs/source-scan.log').read_text().split('\n\tCommand being timed:')[0]);assert not scan['findings']
audit=(f/'logs/build-AuditR6.log').read_text();assert 'Metadata audit passed:' in audit
ax=(f/'logs/build-EndpointR6.log').read_text();assert 'sorryAx' not in ax
(r/'axioms.txt').write_text(ax.split('\n\tCommand being timed:')[0]+'\n')
(r/'metadata-audit.txt').write_text(audit.split('\n\tCommand being timed:')[0]+'\n')
for n in ['module-order.txt','source-manifest.sha256','scan.py','guard.sh','replay.sh']:shutil.copyfile(f/n,r/n)
progress={'status':'partial throughput redesign; no acceptance claim','local_heavy_checks':5000,'local_step_range':[13561,18561],'new_closed_prefix_additions':0,'inherited_closed_prefix':13561,'inherited_remaining_suffix':116110,'inherited_next_lrat_id':38726,'inherited_endpoint':'Percolation.NReplay.not_conjecture20_normalized_after13561 : RemainingSuffixUnsatR5 → ¬ Conjecture20','inherited_endpoint_sources':'inherited.zip and inherited/src/EndpointR5.lean','fresh_packet_endpoint':res['endpoint'],'fresh_packet_modules':len(mods),'remaining_work':['concrete input-mask encoding and generator membership','explicit named hint theorem dependency assembly','full certificate replay to empty clause','unconditional NoMinimalTwoRound5 and refutation','fresh replay of complete assembled packet']}
(r/'progress.json').write_text(json.dumps(progress,indent=2)+'\n');(r/'normalized-progress.json').write_text(json.dumps(progress,indent=2)+'\n')
pilot=res['pilots'][-1]
summary=f'''# Round 6: verified mask checker and heavy pilot, partial

The general bitmask RUP soundness theorem and literal-list encoding equivalence are proved. The optimized 1,000- and 5,000-step heavy pilots passed strict compiler and explicit-module leanchecker replay. No unconditional refutation or new closed normalized-CNF prefix is claimed. Root decides acceptance.

The 5,000-step pilot covers zero-based steps [13561,18561), {pilot['hint_uses']:,} hint uses. Compiler: {pilot['compile_seconds']:.2f} s. Checker: {pilot['checker_seconds']:.2f} s. Combined: {pilot['total_seconds']:.2f} s, {pilot['hints_per_second']:.2f} hints/s, {pilot['speedup_vs_round5_32']:.2f} times round 5's stated approximately 32 hints/s. Peak RSS: {pilot['peak_rss_kib']:,} KiB. These timings include local checks and conditional mask entailments; they exclude the unimplemented concrete input encoding and dependency assembly. The overlapping 1,000-step results and ordinary-elaboration baseline are in results.json.

Endpoint in the fresh experimental packet: `{res['endpoint']}`. Its normalized-unsatisfiability premise remains unproved. NoMinimalTwoRound5 and Percolation.not_conjecture20_unconditional remain unproved.

The complete round 5 archive is preserved byte-identically as inherited.zip (SHA256 9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c). Its 475 modules and conditional endpoint after 13,561 additions remain intact; exactly 116,110 suffix additions remain there. This round does not rebuild that entire inherited replay or claim to replace it. The smaller source-only.zip is a self-contained checker/pilot development packet, not a complete continuation certificate.

Fresh strict packet replay: **{len(mods)}/{len(mods)} compiler passes and {len(mods)}/{len(mods)} explicit-module leanchecker passes**. Compiler wall total: **{res['compiler_seconds']:.2f} s**. Checker wall total: **{res['checker_seconds']:.2f} s**. Combined successful final-packet replay: **{res['total_seconds']:.2f} s**. These are GNU per-process times, excluding development experiments, interrupted/omitted baseline modules, shell overhead and reporting. Source scan and local metadata audit passed. The endpoint and general checker use only propext, Classical.choice and Quot.sound.

The direct-expression builder removes most term elaboration overhead while constructing ordinary Eq.refl proofs checked by both kernels. The compiler checks each added declaration; leanchecker independently rechecks the serialized declarations. No native decision oracle is used.

Development failures and the externally interrupted large ordinary baseline are disclosed in REPRODUCE.md and full logs. No resource cap was raised. Final replay used safe extraction and rolling source/output stamps; the archive was updated with unchanged validated source bytes plus new modules, without copying compiled outputs. All final source bytes are compared with the extraction. No background worker remains at handback.

Files: source-only.zip; inherited.zip; SUMMARY.md; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; NEXT.md; results.json; module-times.json; module-order.txt; progress.json; normalized-progress.json; axioms.txt; metadata-audit.txt; retained-source-comparison.json; inherited-source-comparison.json; certificate-sha256.txt; certificate-shrink-analysis.json; fresh-replay.log; fresh-extracted/logs/; packet/src/; raw.py; pilot.py; MaskBuild and MaskRUP sources.
'''
(r/'SUMMARY.md').write_text(summary)
for n in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','NEXT.md']:
 shutil.copyfile(r/n,p/n);shutil.copyfile(r/n,f/n)
(p/'source-manifest.sha256').write_text(''.join(hashlib.sha256((p/'src'/f'{m}.lean').read_bytes()).hexdigest()+f'  src/{m}.lean\n' for m in mods));shutil.copyfile(p/'source-manifest.sha256',f/'source-manifest.sha256');shutil.copyfile(p/'source-manifest.sha256',r/'source-manifest.sha256')
with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in ['guard.sh','replay.sh','scan.py','module-order.txt','source-manifest.sha256','SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','NEXT.md']+[f'src/{m}.lean' for m in mods]:z.write(p/n,n)
with zipfile.ZipFile(r/'source-only.zip') as z:
 comparison=[]
 for n in z.namelist():
  assert(f/n).read_bytes()==z.read(n)
  assert not n.endswith(('.olean','.ilean','.c','.o'))
  comparison.append({'path':n,'sha256':hashlib.sha256(z.read(n)).hexdigest(),'matches_extraction':True})
(r/'archive-extraction-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
res['source_archive_sha256']=hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest();res['metadata_audit_passed']=True;res['source_scan']=scan
(r/'results.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
export=(f/'logs/build-NormalizedExport.log').read_text().split('BEGIN_DIMACS\n',1)[1].split('END_DIMACS',1)[0].encode()
assert export==(r/'normalized.cnf').read_bytes()
correspondence={'fresh_exact_byte_match':True,'sha256':hashlib.sha256(export).hexdigest(),'variables':1085,'clauses':14698,'units':[1,26,31]}
(r/'generator-correspondence.json').write_text(json.dumps(correspondence,indent=2)+'\n')
res['generator_correspondence']=correspondence
(r/'results.json').write_text(json.dumps(res,indent=2)+'\n')
