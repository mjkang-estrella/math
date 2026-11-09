from pathlib import Path
import json,hashlib,re,datetime,zipfile
D=Path(__file__).resolve().parents[1]; sha=lambda b:hashlib.sha256(b).hexdigest()
v=json.loads((D/'verification.json').read_text()); text=(D/'paper.md').read_text()
assert sum(v['6']['sums'])==342==2*sum(range(1,19))
assert v['6']['sums']==[29,31,29,31,25,29,31,25,31,25,31,25]
assert v['4']['sums']==[22,20,15,22,20,22,20,15]
assert v['6']['classes']=={'25':4,'29':3,'31':5}
assert v['4']['classes']=={'15':2,'20':3,'22':3}
assert [v['6']['odd_cycle_length'],v['4']['odd_cycle_length']]==[7,5]
assert v['source_assertions']['citing_records']==31
assert all(s['trials']==20000 and not s['found'] for s in v['bounded_search'])
assert '2x + 3y + 3z = 2 × (sum of all labels) = 132' in text
raw_tokens=sorted(set(re.findall(r'\d+(?:[.,:/–-]\d+)*',text)))
meta_sources=['sources/review-downloads/arxiv-v1/text.txt','sources/discovery-sources/regular-2022.txt','sources/review-downloads/haslegrave/text.txt','sources/review-downloads/survey/text.txt','evidence/mobius-review-r1/REVIEW.md','evidence/mobius-parent-final-r1/replay-result.json','prior-art-completion.json']
audit={'method':'Fresh integer recomputation in verify.py, plus independent cross-checks here. Numeric strings used as identifiers/dates/bibliographic data are source transcription, not arithmetic propositions. Table cells are generated directly from recomputation.','all_source_numeric_tokens':raw_tokens,'arithmetic_checks':{'M12_total':sum(v['6']['sums']),'M8_total':sum(v['4']['sums']),'M12_order':len(v['6']['sums']),'M12_size':len(v['6']['labels']),'M8_order':len(v['4']['sums']),'M8_size':len(v['4']['labels']),'M12_classes':v['6']['classes'],'M8_classes':v['4']['classes'],'odd_cycles':[7,5],'search_proposals':[s['trials'] for s in v['bounded_search']],'citing_records':31},'metadata_source_files':{p:sha((D/p).read_bytes()) for p in meta_sources},'metadata_note':'Theorem/conjecture numbers, bibliographic volume/page/year/edition data, arXiv/MathDB identifiers and replay version copied from these frozen sources and receipts; document date from environment date. Sections/table/reference numbers are document structure. No claim that metadata identifiers are mathematical computations.'}
(D/'numeric-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n')
qa={'status':'VISUALLY_INSPECTED_ALL_FINAL_PAGES','method':'Poppler PNG rendering followed by tool image inspection of every page; final glyph correction followed by all-page reinspection.','pages':[{'page':i,'image':'qa/page-'+str(i)+'.png','sha256':sha((D/'qa'/('page-'+str(i)+'.png')).read_bytes()),'observed':'Legible, no clipping or overlap; tables/labels legible; notation including universal quantifier visible.'} for i in range(1,6)],'pdf_sha256':sha((D/'paper.pdf').read_bytes()),'layout_receipt':'layout-check.json','note':'Presentation QA is not acceptance or independent mathematical review.'}
(D/'qa/receipt.json').write_text(json.dumps(qa,indent=2)+'\n')
before=json.loads((D/'inputs-before.json').read_text());after={p:sha((D.parent/p).read_bytes()) for p in before};assert before==after
(D/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n');(D/'input-integrity.json').write_text(json.dumps({'status':'UNCHANGED','files':len(before),'before_sha256':sha((D/'inputs-before.json').read_bytes()),'after_sha256':sha((D/'inputs-after.json').read_bytes())},indent=2)+'\n')
res={'mathdb_id':339235,'lane':'mobius-manuscript-r1','status':'DRAFT_READY_FOR_ROOT_REVIEW','accepted':False,'accepted_credit':0,'priority_claim':False,'AI_assistance_explicit':True,'step0':'COMPLETED_BOUNDED_SCREEN_NO_PRIOR_RESULT_FOUND','citing_records_disposed':31,'additional_later_body_screens':9,'limitations':json.loads((D/'prior-art-completion.json').read_text())['limitations'],'main_result':'chi_la(M_12) = 3; refutes the even-n>=4 universal conjecture','remark':'chi_la(M_8)=3; disproves the order-eight theorem; faulty total 132, correct 156','lean_endpoint':'Mobius.conjecture_false','lean_execution_in_this_lane':False,'packet_sha256':v['safe_extraction']['packet_sha256'],'safe_extraction':'PASS','fresh_arithmetic':'PASS','pdf':'paper.pdf','source':['paper.md','scripts/render.py'],'pdf_pages':5,'every_final_page_visually_inspected':True,'archive':'full-dossier.zip','frozen_input_integrity':'UNCHANGED','acceptance_authority':'Root alone'}
(D/'results.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n')
exclude={'manifest.json','manifest.sha256','full-dossier.zip','archive-receipt.json'}
files=sorted(p for p in D.rglob('*') if p.is_file() and p.name not in exclude and not any(x in p.parts for x in ['tmp','cache']))
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in files};(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(D/'manifest.sha256').write_text(sha((D/'manifest.json').read_bytes())+'  manifest.json\n')
with zipfile.ZipFile(D/'full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[D/'manifest.json',D/'manifest.sha256']:z.write(p,str(p.relative_to(D)))
with zipfile.ZipFile(D/'full-dossier.zip') as z:
 assert z.testzip() is None
 for n,h in manifest.items():assert sha(z.read(n))==h
 members=len(z.namelist())
(D/'archive-receipt.json').write_text(json.dumps({'archive':'full-dossier.zip','sha256':sha((D/'full-dossier.zip').read_bytes()),'bytes':(D/'full-dossier.zip').stat().st_size,'members':members,'crc_and_member_hash_test':'PASS','manifest_exclusions':sorted(exclude),'packet_identical':sha((D/'proof-packet-full.zip').read_bytes())==v['safe_extraction']['packet_sha256']},indent=2)+'\n')
print('PASS: frozen inputs unchanged:',len(before),'archive members:',members,'size:',(D/'full-dossier.zip').stat().st_size)
