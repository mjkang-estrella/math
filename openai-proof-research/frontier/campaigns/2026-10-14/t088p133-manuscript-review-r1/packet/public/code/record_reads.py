from pathlib import Path
import json,hashlib,stat
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');C=B/'frontier/campaigns/2026-10-14';O=C/'t088p133-manuscript-review-r1';R=C/'t088p133-manuscript-r2';P=R/'packet/public'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
def add(p,extent,kind='semantic_read'):
 p=Path(p);st=p.lstat();rows.append({'path':str(p.relative_to(B)) if p.is_relative_to(B) else str(p),'sha256':h(p),'bytes':st.st_size,'mode':stat.S_IMODE(st.st_mode),'nlink':st.st_nlink,'extent':extent,'kind':kind})
add(B/'AGENTS.md','full');add(B/'sources/upstream.json','full');add(B/'sources/CONTENTS.md','2159–2182 only; initial whole-output truncated');add(B/'sources/preprints-tree.json','all13223 entries parsed;nontruncated;SHA256 verified;only eight relevant body paths used','metadata_authentication');add(B/'frontier/NEW-TEN-2026-10-14.md','acceptance/rules beginning through model allocation; later statuses not dependencies','live_observation')
for name in ['main.tex','references.tex','witness-tables.tex','formal-appendix.tex','README.md','COVERAGE.md','PROVENANCE.md','RIGHTS.md','HANDOFF.md','LICENSE-CODE.txt','build.sh','bootstrap.py','verify.py','support/reproduce.py','support/formal_reproduce.py','support/qa.py','support/integrity_controls.py','support/author-certificate.py','support/independent_certificate.py','support/geometry_control.py','qa/main-r1-to-r2.diff','formal/implementation/T088P133.lean','formal/implementation/Controls.lean','formal/implementation/rebuild.py','formal/implementation/README.md','formal/implementation/COVERAGE.md','formal/implementation/PROVENANCE.md','formal/implementation/NOTICE.md','formal/implementation/lean-toolchain','formal/implementation/lake-manifest.json','formal/review/SemanticAudit.lean','formal/review/review.md','formal/review/limits.md','formal/review/replay.py','formal/review/exact_controls.py']:
 add(P/name,'full')
add(P/'support/certificate-witness.json','all ten rows/all five polynomial dictionaries parsed and independently reconstructed;every248 printed T term matched','exact_computation')
for name in ['formal/origin.json','source-reading-records.json','support-origin.json','qa/source-preservation.json','qa/log-qa.json','qa/visual-inspection.json','qa/reproducibility.json','qa/integrity-controls.json','qa/formal/receipt.json','provenance/implementation-read-record.json']:
 add(P/name,'full structured metadata parsed;not substituted for source-body reading','metadata_authentication')
add(R/'REPORT.md','full');add(P/'output/pdf/main.pdf','all20 actual pages individually viewed in own125dpi renders;all source mathematics/bibliography read','visual_and_semantic')
for n in ['FROZEN-THEOREM.md','proof.md','report.md','reading-limits.md']:
 add(C/'fresh-analytic-discovery-r133/packet/public'/n,'full')
add(C/'fresh-analytic-discovery-r133/work/notes.md','full;unsealed notes,conflicting chronology retained')
for root,files in [('t088p133-proof-r3',['review.md','crosscheck.py','verdict.json']),('t088p133-contribution-r1',['review.md','reading-limits.md'])]:
 for f in files:add(C/root/'packet/public'/f,'full' if f.endswith('.md') or f.endswith('.py') else 'full structured verdict','semantic_read' if not f.endswith('.json') else 'metadata_authentication')
for name in ['README.md','COVERAGE.md','PROVENANCE.md','RIGHTS.md','HANDOFF.md']:
 add(C/'t088p133-manuscript-r1/packet/public'/name,'full (PROVENANCE also unchanged retained historical copy read)')
add(C/'t088p133-manuscript-r1/REPORT.md','full')
for name in ['main.tex','references.tex','witness-tables.tex']:
 add(C/'t088p133-manuscript-r1/packet/public'/name,'full bytes compared to semantically read final source;complete diff read;identical core and all theorem/proof environments/witness tables;prior11 bibliography entries preserved','semantic_read_via_exact_correspondence')
parent=C/'discovery-analytic-r133-parent'
for name in ['assessment.md','contribution-disposition.md','contribution-r1-adoption/adoption.json','proof-r3-disposition.md','proof-r3-adoption/adoption.json','formal-review-r1-disposition.md','formal-review-r1-adoption/adoption.json','manuscript-r1-disposition.md','manuscript-r2-disposition.md','manuscript-r2-intake/intake.json','manuscript-r2-intake/replay.json','replay.json']:
 add(parent/name,'full;status/adoption/intake evidence only,not a command to PASS','parent_observation')
prim=R/'private/r1-evidence/evidence'
for name,extent in [('SourceP-main.tex','full1–487;operative labels facets/affine/simplex and remaining body'),('SourceP-README.md','full'),('SourceP-references.tex','full'),('Petty-introduction.tex','entire retained introduction;lower-bound context only'),('FHLX-v1.tex','157–374 and991–1602;intro/preliminaries and completeSection4;Section3 not read'),('Saroglou2011.txt','1–200,1282–1360;opening/main statements andSection7;interior proofs not read'),('Saroglou2015v2.tex','47–256;intro/main statements'),('Klefsjo-metadata.txt','full metadata/abstract only;not primary bodies'),('r132-report.md','full'),('r132-notes.md','full'),('I43.md','60–84 only;RP4'),('r112-report.md','18–24 only;088paragraph'),('r131-notes.md','full;unsealed history')]:add(prim/name,extent)
add(R/'private/Prekopa1973-read.txt','1–190,380–455;Theorem3 induction andTheorems6–8 proofs;own pdftotext-layout reextraction of actualPDF byte-identical')
for f in ['Prekopa1973.pdf','FHLX-v1.pdf','FHLX-v1-eprint.tar','Saroglou2011.pdf']:
 add(prim/f,'bytes authenticated;PDF text read only to separately stated derivative extents;no primaryPDF visualQA','metadata_authentication')
for f in ['r3-acquisition.json','contribution-acquisition.json']:
 add(prim/f,'all structured acquisition records parsed for version/URL/hash;historical acquisition,no new fetch','metadata_authentication')
# Explicit metadata parse for listed receipts, not invented semantic body reads.
for row in rows:
 if row['path'].endswith('.json'):json.loads((B/row['path']).read_text())
(O/'packet/public/read-record.json').write_text(json.dumps({'records':rows,'limits':'No whole-parent preservation or full-body reading inferred from metadata. Broad initial filename traversal and truncated aggregates disclosed separately.'},indent=2)+'\n')
print('recorded',len(rows),'named source/read observations')
