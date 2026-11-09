import pathlib,json,hashlib,datetime,xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(L/n).write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
bindings=json.loads((L/'bindings.json').read_text())
history=json.loads((L/'history.json').read_text())
bindings.extend({**r,'mode':'immutable external reference; hash before/after bounded history read'} for r in history if r['hits'])
bindings=list({r['path']:r for r in bindings}.values())
for r in bindings:assert sha(pathlib.Path(r['path']))==r['sha256']
dump('bindings.json',bindings)
admin=[]
for p in sorted((L/'admin').iterdir()):admin.append({'path':str(p.relative_to(L)),'sha256':sha(p),'mode':'administrative snapshot only; not scientific evidence'})
dump('admin-bindings.json',admin)
receipts=[]
for line in (L/'derived.jsonl').read_text().splitlines():
 d=json.loads(line);p=pathlib.Path(d['text']);h=sha(p);pages=p.read_text().split('\f');hits=[]
 for i,t in enumerate(pages,1):
  for s in ['Question 4.4','Question 4.3','Theorem 2.4','Conjecture 5.1','Problem 21','Problem 25','Problem 26','Problem 29','Problem 31','Conjecture 41','Corollary 3.5','Theorem 1.1','Theorem 2.10']:
   if s in t:hits.append({'physical_page':i,'label':s})
 assert h==sha(p);receipts.append({**d,'locators':hits})
dump('source-receipts.json',receipts)
chron=[];ns={'a':'http://www.w3.org/2005/Atom'}
for n in ['versions.xml','cyclo-old.xml','near.xml']:
 p=L/'sources'/n;h=sha(p);root=ET.fromstring(p.read_bytes())
 for e in root.findall('a:entry',ns):
  chron.append({'feed':n,'id':e.findtext('a:id',namespaces=ns),'title':e.findtext('a:title',namespaces=ns),'published':e.findtext('a:published',namespaces=ns),'updated':e.findtext('a:updated',namespaces=ns)})
 assert h==sha(p)
dump('chronology.json',chron)
dump('provenance.json',{'lane':L.name,'completed_utc':now,'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','caps':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'retrieval':'bounded urllib HTTPS via guard; no browser','scientific_sources':'downloads written and hashed before body reading; derived texts bound to unchanged originals; immutable historical references without recursive copying','registry_head_current':None,'registry_limit':'denied GitHub API/raw/codeload/diff/patch routes not retried; no complete current registry clearance','source_freeze_exception':'Initial native bounded read of upstream.json/catalogue header before binding; not used for any scientific deduction or novelty clearance. Recorded in failures.md.','external_mutations':False,'children':False,'git':False})
dump('progress.json',{'status':'research hold; completed specialist screen and two-mechanism sustained attempt','screened_family_groups':14,'ranked_holds':2,'full_results':0,'credit_proposed':0,'counts_snapshot':{'additional':9,'total':39,'next':40},'adjudicator':'root only','best_target':'N Question4.4 canonical-reduction edim-four type bound','missing':'universal arithmetic Apéry-boundary or RF coefficient-packing lemma','verification':'separate guarded verify.py invocation after manifest'})
(L/'SUMMARY.md').write_text('''# r274 handoff

Fourteen grouped specialist question families screened; two ranked research holds; **no full result and zero proposed credit**. This is concentrated numerical-semigroup/algebra breadth, with several source/prior gaps, not fourteen newly open problems. Counts remain root-owned:9 additional/39 total/next40.

Best lead: Moscariello–Strazzanti2020 Question4.4, four-generated canonical-reduction semigroups have type≤4. Sustained two mechanisms: exact reflection of maximal Apéry elements, and one-row RF support elimination. Both leave explicit universal lemmas. The source's known type-four example rigorously blocks transfer of the nearly-Gorenstein type≤3 proof. Countermodels show why either dropping reflection or dropping embedding dimension is invalid. Exact bounded census:35,545 minimal four-generator semigroups with generators≤42, including10,467 canonical; no counterexample. No inference beyond this box.

Reserve: Chomicz2026 closing Conjecture5.1, η≥t+1 for all embedding-dimension-four semigroups. Its actual proof resolves the older boundedness problem, but leaves this sharp bound. RF representation, a cyclotomic family subquestion and CI multiplicity-pair classification are retired before new investment.

Read SCOUTING.md for grouped scopes/limits and discovery.md for proofs of reductions, countermodels and exact missing lemmas. Capped rerun: RUN.sh. Sources/hashes/access/version chronology are bound separately. Current public registry head is unknown; no denied-route retry or bypass. No PROOF.md, Lean, manuscript, shared/count/git/public edits or children. MANIFEST.json excludes itself and verification-receipt.json; the receipt is produced by a separate guarded invocation after writes.
''')
(L/'failures.md').write_text('''# Preserved limitations and unsuccessful routes

- No universal proof/refutation; Apéry reflection does not yet bound four-generator corners, and RF zero patterns alone do not replace absent NG rows. Missing lemmas in discovery.md.
- Known canonical type-four example disproves canonical⇒nearly-Gorenstein and the stronger type≤3 shortcut. Ordinary six-generated semigroup disproves dropping embedding dimension; <9,10,12,13> disproves dropping canonical reduction. These are method countermodels, not source refutations.
- Largest-generator deletion is not a fixed-(m,F) leaf→internal injection: removing6 from <5,6> yields <5,12,18>, still a leaf at F=19. No new result for I.
- Exact source discrepancy: N Question4.3 admits four generators in type2; M Problem23's literal {5,6} statement is not the same source claim. No substitution made.
- Initial lane ls returned absent directory; apply_patch created the assigned lane. Initial native catalogue-header/upstream read preceded scientific freezing; no deduction or novelty assertion uses that material. Main paper bodies and historical r272/root reports were bound before reading. No claim of a flawless prefreeze for that preliminary header.
- pdftotext emitted font-type mismatch warnings for several PDFs. Retained originals and derived hashes permit inspection; no inference from garbled binomial glyphs without surrounding formulas. Some broad read outputs were truncated; focused ranges/labels used for the invested proofs. Unread historical original proofs remain explicitly unverified.
- Source selection achieved14 grouped screens in one specialist area, not wide subject coverage. Several survey-level screens lack original proof bodies. They are deferred, not manufactured survivors. Search false positives retained in feed files.
- All permitted retrievals returned200 in this run. No403/429/challenge was encountered. No retries of previously denied GitHub/raw/codeload/diff/patch, ScienceDirect or Google challenge routes. No historical HEAD loops, browser, proxy or TLS bypass. Current complete registry and exhaustive citing-literature gaps remain open.
- Bound finite checks cannot certify a universal theorem or worldwide novelty; no parameter/helper credit.
''')
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']:files.append({'path':str(p.relative_to(L)),'sha256':sha(p),'size':p.stat().st_size})
dump('MANIFEST.json',{'created_utc':now,'excludes':['MANIFEST.json','verification-receipt.json'],'files':files})
print(json.dumps({'files':len(files),'manifest_sha256':sha(L/'MANIFEST.json')}))
