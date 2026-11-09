from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,xml.etree.ElementTree as ET,os,shutil
p=Path(__file__).resolve().parent.parent;parent=p.parent
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
# Copy the remaining retrieval receipts for the source bodies already included.
for n in ['antimagic-companion.pdf.receipt.json','antimagic-cited.pdf.receipt.json','365453.abs','365453.abs.receipt.json']:
 f=parent/'expanded-corpus-r159/sources'/n;target=p/'evidence/expanded-corpus-r159/sources'/n
 shutil.copyfile(f,target)
# Existing frozen snapshots must remain exactly unchanged.
before=json.loads((p/'inputs-before.json').read_text())
after={n:h(parent/n) for n in before}
(p/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
assert before==after,'Frozen input changed'
pbefore=json.loads((p/'receipts/parent-inputs-before.json').read_text())
pafter={n:h(parent/n) for n in pbefore}
assert pbefore==pafter
(p/'receipts/parent-inputs-after.json').write_text(json.dumps(pafter,indent=2)+'\n')
# All copied frozen evidence must also be byte-identical to its original.
copies=[]
for f in sorted((p/'evidence').rglob('*')):
 if f.is_file():
  original=parent/f.relative_to(p/'evidence')
  assert h(f)==h(original),str(f)
  copies.append({'source':str(original.relative_to(parent)),'copy':str(f.relative_to(p)),'sha256':h(f)})
(p/'receipts/source-copies.json').write_text(json.dumps(copies,indent=2)+'\n')
# Check final PDF text geometry as a complement to actual visual review.
ns={'x':'http://www.w3.org/1999/xhtml'};tree=ET.parse(p/'qa/text.html');pages=tree.findall('.//x:page',ns)
assert len(pages)==5
for pg in pages:
 for w in pg.findall('.//x:word',ns):
  assert float(w.get('xMin'))>=45 and float(w.get('xMax'))<=565,ET.tostring(w)
  assert float(w.get('yMin'))>=40 and float(w.get('yMax'))<=755,ET.tostring(w)
qa={'status':'PASS','pdf_sha256':h(p/'paper.pdf'),'page_count':len(pages),'inspection':'Every page was opened as a rendered PNG and visually inspected by the manuscript worker after the final PDF export. All headings, full proof equations, table rows, bibliographic accents, margins and page footers are readable. No clipping or overlap observed. Bounding-box text check complements the visual inspection.','pages':[{'page':i,'image':'qa/page-'+str(i)+'.png','sha256':h(p/'qa'/('page-'+str(i)+'.png'))} for i in range(1,len(pages)+1)]}
(p/'receipts/pdf-qa.json').write_text(json.dumps(qa,indent=2)+'\n')
a=json.loads((p/'receipts/arithmetic.json').read_text())
result={'status':'DRAFT manuscript and dossier ready for root paper read; no acceptance claimed','mathdb_id':365453,'accepted_credit':0,'mathematics':'No local antimagic labelling with at most three weights on 2(3P2 join O2); chi_la = 4 with ordinary explicit supporting certificate','lean_endpoint':'not_conjecture41 : ¬ Conjecture41','exact_value_four_formalized':False,'packet_sha256':h(p/'source-only.zip'),'paper_pages':len(pages),'checks':{'arithmetic':'PASS','numbers_and_source_metadata':'PASS','safe_packet_extraction':'PASS','packet_byte_identity':'PASS','source_preservation':'PASS','visual_all_pages':'PASS','root_replay':'PASS (copied root report; not rerun by worker)','root_registry_refresh':'present; bounded path screen'},'trust_limits':['Precompiled upstream Lean dependencies trusted','Root and producer audit outputs retained separately','No exhaustive prior-art clearance; OpenAlex incomplete','Older Chan-Lau-Shiu parity analogue credited','Modest significance; no priority claim'],'worker_prohibited_tools_used':False,'child_agents':0,'running_jobs_at_handback':0,'artifacts':['paper.pdf','paper.fodt','paper.md','paper-content.json','PROOF.md','REPRODUCE.md','source-only.zip','full-dossier.zip','MANIFEST.sha256','ARCHIVES.sha256'],'receipts':'receipts/'}
(p/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(p/'SUMMARY.md').write_text('''# MathDB 365453 - DRAFT manuscript dossier

Five-page AI-assisted draft: paper.pdf. Editable source: paper.fodt;
prose source: paper-content.json and scripts/author.py; readable paper.md.
PROOF.md contains the complete case split and supporting four-weight table.

The graph 2(3P2 join O2) has no local antimagic labelling with at most three
weights. Equal null roles contradict parity; different roles yield
12Z <= 435 and 18Z >= 855, hence 36Z <= 1305 < 1710 <= 36Z.
The independently reconstructed table uses weights {45,49,84,99} and proves
chi_la = 4 in ordinary mathematics. The Lean endpoint refutes the literal
universal Conjecture41; the four-weight upper bound is not formalized.

Source author names are Gee-Choon Lau and Wai Chee Shiu, checked against the
publisher PDF. The older Chan-Lau-Shiu disconnected-triangle analogue is credited.
The mixed-role case is the additional obstruction. Significance is modest,
prior-art screens are bounded, OpenAlex is incomplete, and no priority is claimed.
The later formalization-lane publisher-reprint reading updates the review's
historical MDPI access limitation; both records are retained honestly.

Root's replay-result.json and registry-refresh.json are present and copied.
Root reports PASS on its extracted strict replay. This worker ran no Lean,
lake, leanchecker or solver. Root and producer audit counts are reported
separately. No theorem-prover replay is represented as performed here.

Checks: graph and certificate reconstruction, all proof arithmetic and coefficient
identities, numeric metadata provenance, exact packet identity, safe packet
extraction, original tar obstruction equality, common Basics hash, audit recount,
source-copy identity and before/after frozen hashes all PASS. The final five PDF
pages were rendered and each visually inspected; receipt: receipts/pdf-qa.json.

Deliverables: full-dossier.zip, byte-identical source-only.zip, manifest,
source/retrieval receipts, raw MathDB line and its hash, replay/audit evidence,
verification scripts, page PNGs, results.json and REPRODUCE.md.

Zero accepted credit. Root alone accepts; manuscript paper read remains with root.
No publication or upload. No running worker jobs at handback.
''')
print('Final metadata and preserved inputs PASS; PDF QA pages',len(pages))
