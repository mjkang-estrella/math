from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,d):(L/name).write_text(json.dumps(d,indent=2)+'\n')
bindings=json.loads((L/'freeze-bindings.json').read_text())
for r in bindings:
 assert h(L/r['copy'])==r['sha256']
 if r['kind']=='scientific':assert h(Path(r['original']))==r['sha256']
pages=(L/'retrieved/arxiv-v1.txt').read_text().split('\f')
coverage=[]
for page in [1,2,3,4,5,6,12,13,14,15,16,17,18,19,20]:
 coverage.append({'printed_pdf_page':page,'extracted_page_sha256':hashlib.sha256(pages[page-1].encode()).hexdigest()})
write('body-coverage.json',{'source':'retrieved/arxiv-v1','extraction':'retrieved/arxiv-v1.txt','pdf_sha256':h(L/'retrieved/arxiv-v1'),'text_sha256':h(L/'retrieved/arxiv-v1.txt'),'read_body_pages':coverage,'covered':['global definitions and field hypotheses','Lemma1-2 proof bodies','Theorem3 complete derivation Eqs5-13 and Conjectures1-2','Theorem4 complete proof and Corollary5','Theorem15, Corollaries16-17, n8 conditional remark','Section6 complete Eqs16-20, resultant method and Lemmas18-19/Theorem20 proof bodies','Section7 final remarks and references'],'limits':['Not an independent verification of every large integer resultant coefficient','Section4 Fibonacci/gcd development not used as a novelty subsumer','No separately published target/successor proof body located','ArXiv/Crossref/OpenAlex metadata are search/chronology evidence, not proof bodies']})
write('provenance.json',{'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'solo review; no children','assigned_lane':str(L),'target_lane':str(L.parent/'sol-wide-finite-mechanism-scout-r258'),'freeze_bindings':'freeze-bindings.json','freeze_files':len(bindings),'scientific_originals_and_copies_checked_before_after':True,'administrative':'point-in-time snapshots only; no assertion current shared administration is immutable','reused_history':'scientific/history-bindings.json only; no recursive historical copies','primary_pdf_url':'https://arxiv.org/pdf/2102.02081v1','source_submitted_utc':'2021-02-03T14:33:06Z','review_date':'2026-10-30','retrieval_logs':['retrieval.json','followup-retrieval.json'],'guard':{'path':str(guard),'sha256':h(guard),'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'execution_receipts':'tool history guard stderr'},'counts_snapshot':{'additional':9,'total':39,'next':40},'verdicts':{'source':'PASS','math':'PASS both routes, 29 exact checks','substantive':'recommend EXCLUDE: complete routine source Eq6/Eq16 adaptation','novelty':'HOLD no worldwide/current-registry clearance','formal':'feasible assessment only; no certificate/build'},'root_only_accepts':True,'shared_git_public_browser_mathdb_lean_manuscript_mutations':False})
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']:
  files.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':h(p)})
write('final-manifest.json',{'algorithm':'sha256','excluded':['final-manifest.json','verification-receipt.json'],'files':files})
print(json.dumps({'manifest_files':len(files),'original_scientific_files_unchanged':sum(r['kind']=='scientific' for r in bindings)}))
