from pathlib import Path
import hashlib,json,stat,datetime
R=Path.cwd();P=R/'packet/public';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
assert not (R/'FINAL.json').exists(),'Do not reseal an existing final'
for p in (R/'packet').rglob('*'):
 assert not p.is_symlink()
 if p.is_file():assert p.stat().st_nlink==1;p.chmod(0o444)
 elif p.is_dir():p.chmod(0o755)
 else:raise ValueError(str(p))
files={};dirs={'packet':{'mode':0o755}}
for p in sorted((R/'packet').rglob('*')):
 rel=str(p.relative_to(R))
 if p.is_dir():dirs[rel]={'mode':stat.S_IMODE(p.stat().st_mode)}
 elif p.is_file():files[rel]={'bytes':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'sha256':h(p)}
assert len(files)==147 and len(dirs)==22,(len(files),len(dirs))
manifest={'schema':'T088P133-manuscript-r2-exact-v1','files':files,'directories':dirs,'excluded':'Private evidence, build/work/tmp/tools and other non-packet files except three detached envelope anchors. FINAL separately binds private inventories; public verifier does not check their contents.'}
save(R/'packet/MANIFEST.json',manifest)
sourcehash={str(p.relative_to(P)):h(p) for p in sorted(P.glob('*.tex'))}
formalhash={str(p.relative_to(P)):h(p) for p in [P/'formal/implementation/T088P133.lean',P/'formal/implementation/Controls.lean',P/'formal/review/SemanticAudit.lean',P/'formal/origin.json',P/'support/formal_reproduce.py']}
f={'schema':'T088P133-manuscript-r2-final-v1','candidate':'T088P133','round':'manuscript-r2','status':'COMPLETE_FINAL_MANUSCRIPT_IMPLEMENTATION_FOR_INDEPENDENT_REVIEW','runner_as_assigned':'Codex / GPT-6 Astra / high / default service tier','author':'Myeongjin Kang','affiliation':None,'contact':None,'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','count':'18/20 unchanged','formal_integration':'COMPLETED_INDEPENDENTLY_REVIEWED_SCOPED_SUPPORT_INTEGRATED_NO_AUTHOR_REPAIR','support_declarations':21,'control_declarations':20,'independent_review_declarations':15,'full_theorem_formalized':False,'mathematical_theorem_proof_preserved':True,'sparse_terms':248,'original_roots_preserved':True,'original_entries_checked':3682,'public_payload_files':len(files),'public_payload_directories':len(dirs),'pages':20,'manifest_sha256':h(R/'packet/MANIFEST.json'),'report_sha256':h(R/'REPORT.md'),'pdf_sha256':h(P/'output/pdf/main.pdf'),'source_sha256':sourcehash,'formal_origins_and_wrapper_sha256':formalhash,'verifier_sha256':h(P/'verify.py'),'private_evidence_manifest_sha256':h(R/'private/MANIFEST-r2.json'),'private_evidence_named_files':36,'private_cache_inventory_sha256':h(R/'private/build-cache-manifest-r2.json'),'private_cache_named_files':416,'private_evidence_public_verifier_coverage':False,'private_cache_public_verifier_coverage':False,'independent_manuscript_review':'PARENT_TO_DISPATCH_NOT_ASSIGNED_BY_IMPLEMENTATION','self_assigned_correctness_gate':None,'self_assigned_contribution_gate':None,'self_assigned_formal_gate':None,'acceptance':False,'acceptance_ready':False,'portable_release':False,'publication_uploads_submissions_contacts_browser_ui':'STOPPED','sealed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
save(R/'FINAL.json',f)
anchors={'FINAL.json':h(R/'FINAL.json'),'packet/MANIFEST.json':h(R/'packet/MANIFEST.json'),'REPORT.md':h(R/'REPORT.md'),'packet/public/output/pdf/main.pdf':f['pdf_sha256'],**{'packet/public/'+k:v for k,v in sourcehash.items()},**{'packet/public/'+k:v for k,v in formalhash.items()},'packet/public/verify.py':f['verifier_sha256'],'private/MANIFEST-r2.json':f['private_evidence_manifest_sha256'],'private/build-cache-manifest-r2.json':f['private_cache_inventory_sha256']}
save(R/'DETACHED-ANCHORS.json',anchors)
for p in [R/'FINAL.json',R/'packet/MANIFEST.json',R/'REPORT.md',R/'DETACHED-ANCHORS.json']:p.chmod(0o444)
print(json.dumps(anchors,indent=2))
