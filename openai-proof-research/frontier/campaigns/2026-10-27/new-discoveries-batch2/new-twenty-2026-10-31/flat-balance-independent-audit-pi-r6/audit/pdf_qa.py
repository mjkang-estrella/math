import json,hashlib,subprocess,os
lane='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6'
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
pdf=lane+'/input/author-flat-balance-bridges.pdf'
info=subprocess.run(['pdfinfo',pdf],capture_output=True,text=True).stdout
pages={}
for i in (1,2,3):
    p=f'{lane}/manuscript/authorpdf-page-{i}.png'
    pages[f'page{i}']={'png_sha256':sha(p),'bytes':os.path.getsize(p)}
# text extraction cross-checks
txt=subprocess.run(['pdftotext',pdf,'-'],capture_output=True,text=True).stdout
checks={
 'mentions_156_decls':'156 declarations' in txt,
 'claims_14_local_closure':'14 local constants' in txt,
 'claims_endpoint_axioms_choice_quot_only_split':'propext enters only through the Finset extensionality' in txt,
 'pins_lean_5045d00':'5045d0056413266e57c625dcd7c365b10e377c52' in txt,
 'pins_mathlib_d13f23b':'d13f23b723b8a846827a245b89c10fc7d3f11612' in txt,
 'ten_positive_proofs_claim':'TEN' in txt and 'ten positive proofs' in txt,
 'unicode_dash_characters':txt.count('\u2013')+txt.count('\u2014'),
}
rec={'pdf_qa':{
 'skill':'/home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md (read; announced in audit thread)',
 'marker_note':'no new PDF authored by this audit; marker not run (read-only QA). Author PDF preserved untouched.',
 'subject_pdf_sha256':sha(pdf),
 'pdfinfo':info,
 'rendered_pages':pages,
 'render_tool':'pdftoppm -png -r 100',
 'visual_qa':{
   'page_count':3,'page_size':'595x842 A4','rotation':0,
   'findings':'all 3 pages inspected as rendered PNG images: consistent margins/typography; no missing glyphs; no clipped or overlapping text; no black boxes; section numbering 1-8 intact; last page bottom whitespace normal',
   'defects':[]},
 'content_crosscheck_vs_actual_certificate':checks,
 'content_discrepancies_flagged':[
  'R2 paragraph: "transitive constant closure of each endpoint contains 14 local constants" - independent full closure gives 75 (direct endpoint) and 77 (bridges endpoint) local constants; 14 traces to value? without allowOpaque stopping at theorems',
  'R2 paragraph: endpoint axiom closure claimed {Classical.choice, Quot.sound} with propext only via bridge layer - independent collectAxioms+BFS give {propext, Classical.choice, Quot.sound} for BOTH endpoints',
  'Section 1/5 "TEN positive proofs": the controls file contains 11 example blocks (C3 split a/b); ten is the control-count under the C3a/C3b=one-control labeling'],
 'own_pdf_created':False,
 'own_pdf_reason':'author PDF visually clean; factual flags routed to root/Sol review per task; no mathematical or layout change warranted by this audit'},
 'receipt_pdf_sha256':None}
out=lane+'/receipt/pdf-qa.json'
rec['pdf_qa']['receipt_self']='receipt/pdf-qa.json'
open(out,'w').write(json.dumps(rec,indent=2))
print(json.dumps(rec['pdf_qa']['content_crosscheck_vs_actual_certificate'],indent=1))
print('visual+receipt written')
