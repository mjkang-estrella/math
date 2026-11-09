import pathlib,hashlib,json,sys,datetime,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='history':
 terms=['simultaneous edge','Cabello','part-frequency','1001.0313','1001.0610','1001.1017','1001.1100','1001.2156','1601.00332','1601.00506','1601.00926','1601.00943','1601.00969','1601.03938','2001.00181','2001.00257','2001.01463','2001.00653']
 hits=[];seen=0
 for p in B.joinpath('lanes').iterdir():
  if p==L:continue
  for name in ['SCOUTING.md','SUMMARY.md','discovery.md','FINDINGS.md']:
   f=p/name
   if not f.is_file() or f.stat().st_size>200000:continue
   before=sha(f);s=f.read_text(errors='replace');seen+=1
   found=[t for t in terms if t.lower() in s.lower()]
   if found:hits.append({'path':str(f.resolve()),'sha256':before,'terms':found})
   assert sha(f)==before
 dump('history-screen.json',{'files_screened':seen,'method':'top-level named lane reports only; no recursive copy; lexical, not semantic clearance','hits':hits});print(json.dumps(hits,indent=2))
elif sys.argv[1]=='receipts':
 rec=[]
 for p in sorted((L/'sources').glob('*.pdf')):
  before=sha(p);t=p.with_suffix('.txt');s=t.read_text();pages=s.split('\f')
  labels=[]
  for i,page in enumerate(pages,1):
   for line in page.splitlines():
    if any(w in line for w in ['Conjecture ','Question ','Theorem ','Proof of Theorem']):labels.append({'pdf_page':i,'line':line.strip()[:190]})
  rec.append({'pdf':p.name,'sha256':before,'text_sha256':sha(t),'pages':len(pages)-int(not pages[-1].strip()),'labels':labels[:100]});assert sha(p)==before
 dump('source-receipts.json',rec)
 ns={'a':'http://www.w3.org/2005/Atom'};chrono=[]
 for p in (L/'sources').glob('*.xml'):
  for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):
   chrono.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
 dump('chronology.json',chrono)
 dump('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':[9,39,40],'credit':0,'scope':'only assigned lane','source_freeze':'new PDF bytes hashed at retrieval before pdftotext; before/after hash assertions; originals are lane-local frozen copies','administrative':'snapshot only; mutable originals need not remain equal','history_exception':'r269 and r260 reports were initially native-read before immutable-references.json was written; freeze-before-reading was not achieved for these historical administrative/scouting references. No new scientific PDF was read before freeze.','current_registry':'head unknown; prohibited GitHub routes not retried; arXiv searches do not clear public registries','resource':'specified helper_guard; AS/group RSS 512MiB CPU210 wall230; no cap raises; sampled RSS not continuous','external_mutations':False})
elif sys.argv[1]=='manifest':
 dump('MANIFEST.json',{str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']})
elif sys.argv[1]=='verify':
 m=json.loads((L/'MANIFEST.json').read_text());bad=[n for n,h in m.items() if sha(L/n)!=h]
 refs=json.loads((L/'immutable-references.json').read_text());badrefs=[r['path'] for r in refs if sha(pathlib.Path(r['path']))!=r['sha256']]
 for r in json.loads((L/'source-receipts.json').read_text()):
  assert sha(L/'sources'/r['pdf'])==r['sha256'];assert sha((L/'sources'/r['pdf']).with_suffix('.txt'))==r['text_sha256']
 extra=[str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json'] and str(p.relative_to(L)) not in m]
 assert not bad and not badrefs and not extra
 assert not (L/'PROOF.md').exists()
 dump('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'MANIFEST.json'),'files_checked':len(m),'bad':bad,'changed_references':badrefs,'unexpected_files':extra,'scientific_source_checks':'all PDF and derived text hashes match frozen receipts','no_PROOF':True,'acceptance_or_novelty_certified':False});print((L/'verification-receipt.json').read_text())
