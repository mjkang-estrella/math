import pathlib,json,hashlib,datetime,subprocess,sys
D=pathlib.Path(__file__).resolve().parent
rows=json.loads((D/'dispositions.json').read_text());n=sum(not e['complete_self_contained_statement'] for e in rows)
p=D/'SUMMARY.md';p.write_text(p.read_text().replace('Twenty rows are explicitly marked HOLD',str(n)+' rows are explicitly marked HOLD'))
coverage=[]
for e in json.loads((D/'source-provenance.json').read_text()):
 coverage.append({'source':e['url'],'bytes_bound_before_extraction':True,'derivative_bound_before_search':True,'whole_body_read':False,'full_dependencies_audited':False,'successor_bodies_audited':False,'selected_scope':{'2308.06670':'Preliminaries, independent-set theorem4.1 proof, conclusion; no AGX search match; not asserted full-source absence proof','2306.08457':'Introduction ConjectureB, Theorem1.1, surrounding known homogeneous/monomial cases; cited counterexample body not read','2401.11496':'Conjecture context and n3 alternating-polynomial transformation proof excerpts; general determinant diagnostic','2407.07553':'Section3.2 Proposition18 and selected AppendixA.5 proof; model matrices selected; bilinear inequality not independently justified','2408.03921':'Theorem4.1 statement and Conjecture4.5 with preceding fixed-label motivation'}[e['path'].replace('.html','')], 'registry':'HOLD unavailable; zero requests'})
(D/'source-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
# Build exact local payload manifest. No original data copied.
excluded=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
m={'schema_version':1,'excluded_exact_paths':excluded,'files':files};(D/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
# Named final receipt exists before exact-set verification; populated only after success.
(D/'final-verification-receipt.json').write_text('{}\n')
p=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
print(p.stdout,p.stderr);assert p.returncode==0
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':p.returncode,'result':json.loads(p.stdout),'scope':'Integrity only; zero math or novelty clearance'}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
