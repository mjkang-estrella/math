from pathlib import Path
import json,hashlib,shutil,stat
R=Path(__file__).resolve().parents[1];B=R.parent;S=R/'public-source';M=B/'t088p133-manuscript-r2';P=M/'packet/public';V=B/'t088p133-manuscript-review-r1';map={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cp(src,dst,role):
 dest=S/dst;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
 map[dst]={'origin':src.relative_to(B).as_posix(),'sha256':sha(src),'bytes':src.stat().st_size,'treatment':'unchanged bytes','role':role}
for f in ['main.tex','references.tex','witness-tables.tex','formal-appendix.tex','output/pdf/main.pdf','LICENSE-CODE.txt','support-origin.json','source-reading-records.json']:
 cp(P/f,'packet/public/'+f,'reviewed manuscript, rights or origin metadata')
for f in ['author-certificate.py','independent_certificate.py','certificate-witness.json','geometry_control.py','reproduce.py','formal_reproduce.py','qa.py']:
 cp(P/'support'/f,'packet/public/support/'+f,'unchanged exact/formal support; geometry diagnostic retained only')
for f in ['T088P133.lean','Controls.lean','rebuild.py','lean-toolchain','lake-manifest.json','NOTICE.md','LICENSE-CODE.txt','COVERAGE.md','PROVENANCE.md','validation/types-axioms.log','validation/support.log','validation/controls.log']:
 cp(P/'formal/implementation'/f,'packet/public/formal/implementation/'+f,'reviewed formal source, pins, notices and expected logs')
for f in ['SemanticAudit.lean','exact_controls.py','NOTICE.md','LICENSE-CODE.txt','review.md','limits.md','evidence/review-types-axioms.log']:
 cp(P/'formal/review'/f,'packet/public/formal/review/'+f,'independent semantic audit, rights, exact controls and expected type log')
cp(P/'formal/origin.json','packet/public/formal/origin.json','original 53-file origin ledger; selection explained in assembly map')
for f in ['README.md','COVERAGE.md','PROVENANCE.md','RIGHTS.md','HANDOFF.md']:
 cp(P/f,'provenance/manuscript-r2/'+f,'historical implementation-at-time-written record; not current commands')
for f in ['provenance/r1-PROVENANCE.md','provenance/r1-RIGHTS.md','provenance/r1-source-reading-records.json']:
 cp(P/f,'provenance/'+Path(f).name,'historical original provenance and reading boundaries')
for name,root in [('manuscript-r2',M),('manuscript-review-r1',V)]:
 for f in ['FINAL.json','packet/MANIFEST.json','REPORT.md']:
  cp(root/f,'provenance/'+name+'/'+Path(f).name,'historical externally authenticated envelope; original seal is not release coverage')
for f in ['review.md','obligations.md','limits.md','read-record.md']:
 cp(V/'packet/public'/f,'provenance/manuscript-review-r1/'+f,'completed independent manuscript review, attributed')
for f in ['source-comparison.json','tex-log-qa.json','visual-qa.json','formal-receipt.json','independent-exact.json']:
 cp(V/'packet/public/evidence'/f,'provenance/manuscript-review-r1/evidence/'+f,'attributed independent evidence; not new release-run result')
cp(V/'packet/public/code/independent_exact.py','packet/public/support/independent_exact.py','unchanged independent direct-residue/printed-TeX checker; new runner supplies its relative layout')
cp(V/'packet/public/LICENSE-CODE.txt','provenance/manuscript-review-r1/LICENSE-CODE.txt','retained code notice')
parent=B/'discovery-analytic-r133-parent'
for f in ['contribution-disposition.md','proof-r3-disposition.md','formal-review-r1-disposition.md','manuscript-review-r1-disposition.md','contribution-r1-adoption/adoption.json','proof-r3-adoption/adoption.json','formal-review-r1-adoption/adoption.json','manuscript-review-r1-adoption/adoption.json']:
 cp(parent/f,'provenance/parent/'+f,'adopted separate gate; historical next-step text superseded by release README')
# Public tool-input metadata derived after FINAL-bound private inventory authentication; no private body is copied.
cache=json.loads((M/'private/build-cache-manifest-r2.json').read_text())['files'];files={p.removeprefix('build/cache/'): {k:v[k] for k in ['bytes','sha256']} for p,v in cache.items() if p.startswith('build/cache/')}
tools={'tectonic_version':'0.17.0','tectonic_sha256':'a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da','source_date_epoch':1792454400,'tex_cache_files':files,'origin_inventory_sha256':sha(M/'private/build-cache-manifest-r2.json'),'lean':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','generic_inputs':['Python 3.10+ standard library','SymPy 1.14.0 with mpmath 1.3.0','Poppler pdftoppm, pdftotext, pdfinfo','Linux runtime and system font/fontconfig environment','Lean compiler/runtime plus precompiled mathlib and eight locked auxiliaries'], 'boundary':'Tool/cache bytes excluded. Metadata pins do not establish complete supply-chain authenticity. Only own Lean source rebuilt.'}
(S/'tool-inputs.json').write_text(json.dumps(tools,indent=2,sort_keys=True)+'\n')
selection={'schema':'T088P133-release-assembly-map-v1','copied':map,'generated':{},'exclusions':['all protected primary/upstream/history/search bodies and their renders','all engine/dependency/cache binaries','old formal/review/replay.py and historical inventory/verifier/sealer execution paths','redundant historical build/QA/administrative files and manuscript renders'],'origin_ledger_scope':'formal/origin.json retains all 53 original entries unchanged; only listed selected entries are distributed. Omitted entries are not execution dependencies.','release_owned_files':'All other manifest payloads are new original release routing/documentation/metadata; their exact hashes are in MANIFEST.json.'}
(S/'assembly-map.json').write_text(json.dumps(selection,indent=2,sort_keys=True)+'\n')
(R/'work/named-parent-before.json').write_text(json.dumps({str(parent/f):sha(parent/f) for f in ['manuscript-r2-brief.txt','proof-r3-disposition.md','proof-r3-adoption/adoption.json','formal-review-r1-disposition.md','formal-review-r1-adoption/adoption.json','manuscript-r2-disposition.md','manuscript-r2-intake/intake.json','manuscript-review-r1-disposition.md','manuscript-review-r1-adoption/adoption.json','replay.json','contribution-disposition.md','contribution-r1-adoption/adoption.json']},indent=2)+'\n')
print('selected unchanged files',len(map),'declared cache files',len(files))
