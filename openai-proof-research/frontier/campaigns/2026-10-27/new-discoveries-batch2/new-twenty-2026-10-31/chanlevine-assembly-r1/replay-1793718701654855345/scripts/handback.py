import pathlib,json,hashlib,re,zipfile
lane=pathlib.Path(__file__).resolve().parent.parent
receipt=json.loads((lane/'logs/latest-replay.json').read_text());assert receipt['returncode']==0
root=pathlib.Path(receipt['directory'])
validation=json.loads((root/'logs/validation-result.json').read_text());assert validation['status']=='PASS'
build=json.loads((root/'logs/build-result.json').read_text());assert build['status']=='PASS' and len(build['records'])==75
merge=json.loads((lane/'merge-manifest.json').read_text());manifest=json.loads((lane/'formal-manifest.json').read_text())
assert all(hashlib.sha256((lane/'formal'/n).read_bytes()).hexdigest()==h for n,h in manifest.items())
assert all(manifest[n]==r['sha256'] for n,r in merge['modules'].items())
endpoint=(root/build['records']['ChanLevineFinal']['lean']).read_text()
assert "'ChanLevine.mathdb_338887' depends on axioms: [propext, Classical.choice, Quot.sound]" in endpoint
rss=[]
for p in (root/'logs').glob('*.log'):
 rss += [int(v) for v in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
archive=lane/'chanlevine-assembly-source.zip'
with zipfile.ZipFile(archive) as z:
 assert sum(n.startswith('formal/') and n.endswith('.lean') for n in z.namelist())==75
 assert not any(n.endswith(('.olean','.ilean','.so','.pyc')) for n in z.namelist())
audit=validation['audit']
result={'mathdb_id':338887,'lane':'chanlevine-assembly-r1','status':'UNCONDITIONAL_ENDPOINT_VALIDATED_PENDING_ROOT_REVIEW','self_accepted':False,'credit_requested':0,'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','archive_hashes':merge['archives'],'merged_modules':merge['modules'],'shared_module_names':merge['shared_names'],'shared_module_count':36,'inherited_module_count':74,'conflicts':0,'frozen_byte_identical':True,'added_modules':{'ChanLevineFinal.lean':manifest['ChanLevineFinal.lean']},'endpoint':'ChanLevine.mathdb_338887','corollary':'ChanLevine.recurrent_count_depends_only_on_gcd','endpoint_unconditional':True,'endpoint_axioms':['propext','Classical.choice','Quot.sound'],'remaining_props':[],'merge_rebuild':{'status':'PASS','strict_modules':74,'leanchecker_modules':74,'result':'logs/build-result.json'},'fresh_replay':{**receipt,'status':'PASS','strict_modules':75,'leanchecker_modules':75,'resumable':True,'max_reported_rss_kib':max(rss)},'audit':audit,'negative_controls':validation['negative_controls'],'positive_controls':validation['positive_controls'],'source_archive':{'path':archive.name,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_only':True,'safe_paths':True,'fresh_extraction_matches':True},'resource_caps':{'cpus':2,'cpu_seconds':120,'wall_seconds':140,'rss_kib':6291456,'MALLOC_ARENA_MAX':'2','lean_args':['-j1','-M3500','-DwarningAsError=true'],'serial':True},'writes_outside_lane':False,'child_agents':0,'git_operations':0,'shared_ledger_edits':0,'uploads_external_messages_browser_tabs':0,'background_processes_left':0,'novelty_acceptance_claimed':False,'development_failures_retained':True}
(lane/'results.json').write_text(json.dumps(result,indent=2))
summary=f"""# Assembly handback — root review pending

`ChanLevine.mathdb_338887` is proved unconditionally in formal/ChanLevineFinal.lean by applying the unchanged round-1 `mathdb_338887_conditional_full` to all seven discharged Props. No bridge hypothesis remains. The exact statement includes source component existence and uniqueness, recurrent-component status, and equal cardinality for equal gcds. The direct corollary is `recurrent_count_depends_only_on_gcd`. Both endpoints use only propext, Classical.choice and Quot.sound.

All three input archive hashes match the brief. The union has 74 inherited modules; the 36 shared names are byte-identical, with zero conflicts. Every inherited source is unchanged. ChanLevineFinal.lean is the only new formal module. merge-manifest.json and results.json inventory every inherited module with its hash and packet origins; formal-manifest.json includes the endpoint hash.

The initial merged tree passed strict Lean and leanchecker on all 74 modules. The delivered source-only archive was safely extracted into a new empty directory, its 75 source hashes verified, and all 75 modules rebuilt strictly and checked with leanchecker. Every expensive child ran serially with the specified resource caps. Maximum reported RSS in the fresh replay was {max(rss):,} KiB. Logs are unique and retained; build receipts permit resumption.

The final declaration audit seeds every local declaration, including generated/private declarations, in ChanLevineFinal's local module import closure. It reads opaque bodies with allowOpaque := true and adds constructor dependencies. There are {audit['local_declarations']:,} local seeds and {audit['upstream_declarations']:,} upstream dependencies, {audit['total_closure']:,} declarations in total. An independent Python traversal of the emitted dependency edges gives exactly the audited set. Unsafe, partial and _unsafe_rec counts are zero. LOCAL extern/implemented_by metadata is absent. There are {len(audit['UPSTREAM_metadata'])} UPSTREAM entries with executable metadata, individually listed in results.json; this is not claimed to be zero. Only the three permitted axioms occur. The audit covers reachable declarations from all local seeds, not unrelated imported tactic/compiler declarations.

All three expected-failure controls passed: an application across different gcds, omission of positive level, and reversal of the rotor weight convention. Two positive controls also passed. These are interface sensitivity checks; rejection of an altered proof is not itself a counterexample proof. STATEMENT-CORRESPONDENCE.md maps the endpoint to cached Conjecture 8.3, Example 3.11, Definition 5.2, Definition 4.8 and the source level/weight/component/count definitions.

Source archive: `{archive.name}`, SHA-256 `{result['source_archive']['sha256']}`. Fresh replay directory: `{root.name}`. Full replay receipt: logs/latest-replay.json. Audit details: `{root.name}/logs/assembly-audit.json`. REPRODUCE.md documents a fresh replay and resumption. Initial naive source scans matched diagnostic strings/comments; the corrected scan excluded Lean comments and diagnostic strings. The first endpoint compile failed because CountFinal was not imported explicitly; the failed archive, fresh extraction and logs are retained. Adding that import fixed the assembly without changing any inherited source.

All writes stayed in this lane. No child agents, git operations, shared ledger edits, network access, uploads, external messages or browser tabs were used. No background process remains. This is an assembly certificate for root review, not self-acceptance, credit, novelty clearance, or an independent adversarial review. Root decides.
"""
(lane/'SUMMARY.md').write_text(summary)
print(json.dumps({'status':result['status'],'axioms':result['endpoint_axioms'],'audit_total':audit['total_closure'],'archive_sha256':result['source_archive']['sha256']},indent=2))
