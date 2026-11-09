from pathlib import Path
import hashlib,json,zipfile,ast
b=Path('..');o=Path('.');h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
initial=json.loads(Path('inputs-before.json').read_text());after={n:h(b/n) for n in initial};assert initial==after
Path('inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
supp=json.loads(Path('supplemental-inputs-before.json').read_text());suppafter={n:h(Path(n)) for n in supp};assert supp==suppafter
Path('supplemental-inputs-after.json').write_text(json.dumps(suppafter,indent=2)+'\n')
Path('receipts/frozen-integrity.json').write_text(json.dumps({'status':'PASS','initial_files':len(initial),'supplemental_files':len(supp),'all_unchanged':True,'initial_manifest_sha256':h(Path('inputs-before.json')),'after_manifest_sha256':h(Path('inputs-after.json')),'scope':'all selected assigned immutable inputs plus later-added resource receipts and font inputs; root ongoing replay was neither run nor bound as immutable'},indent=2)+'\n')
copies={}
for p in Path('evidence').rglob('*'):
 if not p.is_file():continue
 origin=str(p.relative_to('evidence'));expected=initial.get(origin) or supp.get(str((b/origin).resolve()))
 assert expected and h(p)==expected,str(p)
 copies[str(p)]={'origin':origin,'sha256':expected}
Path('COPY-RECEIPT.json').write_text(json.dumps({'status':'PASS','copies':copies,'formal_source_location':'nut-source-only.zip; every formal source checked by verify_packet.py','packet_identity_sha256':h(Path('nut-source-only.zip'))},indent=2)+'\n')
ast.parse(Path('safe-extracted/replay.py').read_text())
for p in o.glob('*.py'):ast.parse(p.read_text())
Path('receipts/driver-syntax.json').write_text(json.dumps({'status':'PASS','method':'ast.parse; no execution of replay.py','driver':'safe-extracted/replay.py'},indent=2)+'\n')
results={
 'status':'DRAFT_DOSSIER_COMPLETE_PENDING_ROOT_ACCEPTANCE', 'mathdb_id':'365943',
 'endpoint':'Nut8.no_cubic_8circulant_nut : Nut8.Target','credit':0,
 'paper':{'pdf':'nut-draft.pdf','source':'paper.md','renderer':'build_paper.py','pages':10,'visual_qa':'PASS'},
 'verification':{'safe_extraction_manifest_replay':'PASS','frozen_inputs_unchanged':'PASS','forbidden_source_command_scan':'PASS','source_packet_byte_identity':'PASS','pdf_all_pages_visual_qa':'PASS','full_lean_replay_this_lane':'NOT_RUN_BY_EXPLICIT_ASSIGNMENT','fresh_full_replay_acceptance':'PENDING_ROOT','spot_compiles_this_lane':0},
 'inherited_evidence':{'development_endpoint_checker':'PASS','development_audit_shards':128,'audit_records':46045,'distinct_declaration_names':46022,'repeated_generated_companion':{'name':'Nut8.unsignedPatterns.eq_1','occurrences':24},'development_negative_controls_passed':18,'independent_supports':194,'independent_signed_matrices':9172,'nonzero_determinants':8208,'zero_cofactors':964,'review_acceptance':'HOLD pending root full replay'},
 'packet':{'path':'nut-source-only.zip','sha256':h(Path('nut-source-only.zip')),'source_manifest_entries':1289,'lean_source_files':1279,'scheduled_modules':1151,'endpoint_closure_modules':1024},
 'limits':{'cpu_slots':2,'cpu_seconds':120,'wall_seconds':140,'sampled_rss_gib':6,'MALLOC_ARENA_MAX':2,'heavy_processes_concurrent_max':1},
 'integrity':{'initial_input_count':len(initial),'supplemental_input_count':len(supp),'unchanged':True},
 'remaining_root_gates':['Complete strict fresh extracted proof replay, all checkers, audit and controls.','Read and approve draft paper.','Refresh public registries and adjudicate retained bounded novelty/access limits.','Root alone decides acceptance and credit.'],
 'restrictions_observed':{'child_agents':0,'git_operations':0,'shared_ledger_edits':0,'outside_lane_writes':0,'network_requests':0,'browsers':0,'external_messages':0,'publication_uploads':0,'background_jobs_launched':0},
 'receipt_scope_warning':'No complete fresh Lean replay PASS exists in this manuscript lane. Local extraction PASS and inherited development PASS must not be represented as that result.'}
Path('results.json').write_text(json.dumps(results,indent=2)+'\n')
Path('SUMMARY.md').write_text('''# Nut8 manuscript and dossier - DRAFT

Created a ten-page AI-assisted manuscript, **No cubic 8-circulant nut graph: a signed-quotient obstruction**, for MathDB 365943. The exact endpoint is `Nut8.no_cubic_8circulant_nut : Nut8.Target`. Zero accepted credit; root alone accepts.

Deliverables: `nut-draft.pdf`, editable `paper.md` and `build_paper.py`, continuous ordinary `PROOF.md`, `STATEMENT-CORRESPONDENCE.md`, `REPRODUCE.md`, both ZIPs, source/module/dossier manifests, exact raw MathDB line with hash, frozen source/evidence copies, resource receipts, and all ten rendered QA pages.

`nut-source-only.zip` is byte-identical to r7q's final packet: SHA-256 `e4710a538ed6ef60e6649fcb288dd873db52ce613eeddca564627f39c96ef402`. Safe extraction/manifest replay PASS: 1,290 ZIP members, 1,289 manifest entries and all 1,279 Lean sources match the frozen originals. No compiled binaries, unsafe paths, symlinks or forbidden source commands were found. Every PDF page was individually inspected visually. All initially bound and supplemental inputs remain unchanged; see receipts/frozen-integrity.json.

No Lean process was run. The inherited development checker, 128 audit shards and 18 controls report PASS; independent review verified 194 supports and all 9,172 matrices. The audit is correctly described as 46,045 records over 46,022 distinct printed names, with Nut8.unsignedPatterns.eq_1 occurring 24 times. The six compilation fixes and their actual resource receipts are copied. Large audit-body logs remain in the immutable originating lane and are indexed rather than duplicated.

The full fresh Lean replay PASS is NOT claimed: root is running it separately in nut-parent-final-r1. The r7q snapshot's corrected extraction remained incomplete. No local extraction result or development audit is relabelled as final replay. Root must complete that gate, read the paper, refresh registries and judge bounded novelty/access limits. The dossier preserves the unrelated arXiv:1808.08747 metadata error without treating it as related literature. No priority claim is made.

No child agents, git, outside-lane writes, shared ledger edits, browser, network requests, external messages, upload or publication. All guarded work was sequential; no background jobs were started or remain from this lane. The first PDF build failed because an assumed font path was absent; its receipt is retained, and the final successful build used the supplied frozen fonts.
''')
# ZIP manifest excludes self-referential/detached outputs, temp extraction and finalizer's running receipt.
exclude={'DOSSIER-MANIFEST.json','archive-hashes.json','nut-full-dossier.zip','receipts/finalize-resources.json','receipts/archive-verification.json'}
files=[p for p in o.rglob('*') if p.is_file() and not any(x in ['tmp','safe-extracted','__pycache__'] for x in p.parts) and str(p) not in exclude]
manifest={str(p):h(p) for p in sorted(files)}
Path('DOSSIER-MANIFEST.json').write_text(json.dumps({'sha256':manifest,'exclusions':sorted(exclude),'excluded_directories':['tmp','safe-extracted','__pycache__'],'note':'Detached packaging/resource receipts avoid circular archive hashes.'},indent=2)+'\n')
with zipfile.ZipFile('nut-full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted(files+[Path('DOSSIER-MANIFEST.json')]):z.write(p,str(p))
with zipfile.ZipFile('nut-full-dossier.zip') as z:
 assert z.testzip() is None
 for n,v in manifest.items():assert hashlib.sha256(z.read(n)).hexdigest()==v
Path('archive-hashes.json').write_text(json.dumps({n:h(Path(n)) for n in ['nut-source-only.zip','nut-full-dossier.zip']},indent=2)+'\n')
Path('receipts/archive-verification.json').write_text(json.dumps({'status':'PASS','full_dossier_payload_files':len(manifest),'zip_crc':'PASS','all_manifest_file_hashes_match':True,'source_packet_sha256':h(Path('nut-source-only.zip')),'full_dossier_sha256':h(Path('nut-full-dossier.zip'))},indent=2)+'\n')
print(json.dumps({'status':'PASS','bound_unchanged':len(initial)+len(supp),'payload_files':len(manifest),'full_dossier_bytes':Path('nut-full-dossier.zip').stat().st_size}))
