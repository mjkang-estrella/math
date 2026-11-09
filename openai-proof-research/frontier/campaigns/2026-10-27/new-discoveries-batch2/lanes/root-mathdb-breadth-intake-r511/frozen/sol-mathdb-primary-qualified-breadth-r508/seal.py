import pathlib,json,hashlib,subprocess,sys,datetime,collections
P=pathlib.Path(__file__).resolve().parent
ss=json.loads((P/'statements.json').read_text());notes={}
for line in (P/'technical-notes.tsv').read_text().splitlines():
 a,b,c=line.split('\t',2);notes[int(a)]=(b,c)
assert len(notes)==50 and set(notes)=={s['ID'] for s in ss}
ds=[]
for s in ss:
 d={k:v for k,v in s.items() if k!='record'};status,note=notes[s['ID']]
 d.update(title=s['record']['title'],source_url=s['record']['source_url'],disposition=status,individual_assessment=note,record_statement_review='literal_full_statement_read',accepted_credit=0,prior_cleared=False,full_dependency_audit=False,current_registry_cleared=False,full_scope_new_proof=False,primary_body_review=s['ID'] in [383344,383495,392481,405217],evidence_limits='See source-coverage.json; finite checks are not proofs. No promotion.')
 ds.append(d)
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
write('dispositions.json',ds);write('proposals.json',[])
write('coverage.json',{'assigned':50,'literal_full_statements_read':50,'selected_primary_bodies':4,'complete_extracted_local_bodies_read':2,'full_dependency_audits':0,'new_full_scope_proofs':0,'qualified_hypotheses':0,'credit':0,'baseline_reported_reviews':3733,'root_reconciliation_potential':3783,'root_reconciliation_potential_limit':'This lane only; root must reconcile and handle other disjoint batches. No shared coverage change.', 'dispositions':dict(collections.Counter(d['disposition'] for d in ds))})
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in {'manifest.json','final-verification-receipt.json'}:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
write('manifest.json',dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files))
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
write('final-verification-receipt.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,manifest_sha256=hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest(),manifest_size=(P/'manifest.json').stat().st_size,guard='fixed helper_guard.py parent: 512MiB AS/groupRSS, CPU210s, wall230s unchanged',scientific_acceptance=False))
print(r.stdout);print('exit',r.returncode);print('manifest',hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest(),(P/'manifest.json').stat().st_size);sys.exit(r.returncode)
