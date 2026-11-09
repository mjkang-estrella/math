import pathlib,json,hashlib,re,datetime,collections
L=pathlib.Path(__file__).resolve().parent;B=L.parent
J=lambda p:json.loads(p.read_text())
notes={}
for line in (L/'technical-notes.tsv').read_text().splitlines():
 i,s,n=line.split('\t');notes[int(i)]=(s,n)
rows=J(L/'records.json');assert len(notes)==len(rows)==50
sources=J(L/'sources.json');passages=J(L/'read-passages.json')
for s in sources:
 key=pathlib.Path(s['text']).stem;text=pathlib.Path(s['text']).read_text();v=re.search(r'arXiv:\s*'+re.escape(key)+r'v\d+[^\n]*',text)
 s['version']=v.group(0) if v else 'version not identifiable from extracted PDF; served bytes pinned by SHA256'
 s['read_level']='selected question/result passages only; not whole body'
 s['whole_body_read']=False;s['dependency_audit']=False;s['passage_ranges_1based']=next(x['ranges'] for x in passages if x['key']==key)
 s['range_caution']='Ranges use Python splitlines including form-feed page breaks. Additional manually read passages for 1103.3858 Conj3.5, 1104.3528 definitions1.2/1.3 Prop1.4 Conj1.5; automated anchors for those two missed target and are not credited as question reads.'
(L/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];status,note=notes[i];key=r['source_url'].rsplit('/',1)[-1];src=next(s for s in sources if pathlib.Path(s['text']).stem==key)
 if i==321038:status='HOLD_PRIOR_REPORT'
 out.append({'mathdb_id':i,'title':r['title'],'canonical_url':r['canonical_url'],'literal_statement':r['statement'],'literal_statement_read':True,'statement_sha256_utf8':x['statement_sha256'],'canonical_record_sha256':x['canonical_record_sha256'],'original_chunk':x['original_chunk'],'original_line':x['original_line'],'original_line_sha256':x['line_sha256'],'disposition':status,'full_scope_mechanism_or_obstacle':note,'source_level':{'url':r['source_url'],'version':src['version'],'sha256':src['pdf_sha256'],'read':'question/result passages; definitions only as specifically identified, no whole-body claim','locator':'technical-notes.tsv and read-passages.json; corrected manual anchors documented in sources.json'},'proof_level':'No new full-scope proof. Published theorem passage only for source exclusions; no whole dependency audit.','registry_level':'HOLD: zero MathDB requests under inherited429 restriction; no global priority clearance. Cached record status not authoritative.','closest_successors':{'status':'HOLD','scope':'No independent successor body audit except source-internal later theorem passages; dismal title query only metadata, not review.'},'bounded_check':({'status':'EXECUTED','artifact':'bounded-checks.json','scope':'T6 known source witness'} if i==321528 else {'status':'EXECUTED','artifact':'bounded-checks.json','scope':'exhaustive binary factor supports k=2..10; no all-k inference'} if i in [321853,321854] else {'status':'NOT_EXECUTED','reason':'Parked before proof investment; no finite check would certify universal scope.'}),'certificate_size':('15 vertices; explicit cut9' if i==321528 else '9217 ordered binary factor pairs, shared check' if i in [321853,321854] else 'none produced'),'formal_dependencies':'No Lean or formalization; prospective source dependencies in technical note remain unaudited.','strongest_objection':'Already in cited source; no discovery credit.' if status.startswith('EXCLUDE') else 'Full-scope proof and successor/registry clearance absent; finite examples or source adaptations earn no credit.','prior_gaps':'No novelty inferred from absent search hits. MathDB registry unavailable; literature successor and dependency coverage bounded.','proposed_credit':0})
(L/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(L/'proposals.json').write_text('[]\n')
f=J(L/'failures.json');f.extend([{'kind':'access_constraint','status':'HOLD','details':'ZERO MathDB requests (inherited429); inherited AIM/Kourovka/EGRES, AIProofWatch, rigid-body and triangle-gap denied routes parked; no retry or alternate route.'},{'kind':'coverage_gap','status':'HOLD','details':'Successor proof bodies not independently audited. Two bounded arXiv discovery feeds are metadata only. Primary-PDF retrieval all45 succeeded; not a whole-body or dependency audit.'},{'kind':'locator_failure','preserved':'target-passages.txt','details':'1106.0369 Unicode name aliases did not match; correct Conj2 passage read using interesting anchor. 1103.3858 and1104.3528 generic anchors missed question, corrected manually; original locator output retained.'}]);(L/'failures.json').write_text(json.dumps(f,indent=2)+'\n')
# Record query provenance separately: exact returned bytes, metadata only.
q=[]
for stem,url in [('dismal-successors','https://export.arxiv.org/api/query?search_query=all%3Adismal&start=0&max_results=10&sortBy=submittedDate&sortOrder=descending'),('dismal-title-successors','https://export.arxiv.org/api/query?search_query=ti%3Adismal&start=0&max_results=20&sortBy=submittedDate&sortOrder=descending')]:
 p=L/'sources'/(stem+'.xml');q.append({'url':url,'version':'Atom response dated2026-10-31; query bounded','utc':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'level':'metadata only, no source proof reviewed','read':'First feed cover+first entry only; title-filter feed returned2 entries read. Absence gives no priority clearance.'})
(L/'successor-queries.json').write_text(json.dumps(q,indent=2)+'\n')
print(collections.Counter(x['disposition'] for x in out))
