import pathlib,json,hashlib,xml.etree.ElementTree as E,re,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
ledger=json.loads((L/'administrative/ledger.json').read_text());context=json.loads((L/'administrative/prior-campaign-context.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
n={'a':'http://www.w3.org/2005/Atom'};root=E.fromstring((L/'primary/versions.atom').read_bytes())
chron=[]
for e in root.findall('a:entry',n):
 chron.append({k:e.findtext('a:'+k,default='',namespaces=n).strip() for k in ['id','title','published','updated']})
write('chronology.json',chron);print(json.dumps(chron,indent=1))
access=[json.loads(s) for s in (L/'access.jsonl').read_text().splitlines()]
bindings=[]
for r in access:
 if 'file' in r:
  p=L/r['file'];assert sha(p)==r['sha256'];bindings.append(r)
write('primarybindings.json',bindings)
coverage={}
for p in (L/'texts').glob('*.txt'):
 lines=p.read_text().splitlines();ranges=[]
 for i,s in enumerate(lines):
  if re.match(r'^\s*(Conjecture|Theorem [123]\.|Proposition [235]\.|4.6\s+Update|Lemma 2.1)',s):ranges.append([max(1,i-1),min(len(lines),i+22)])
 coverage[p.name]={'sha256':sha(p),'target_passages':ranges,'scope':'Selected extraction passages; supplemental ranges explicitly documented in SCOUTING. Not full-paper coverage.'}
write('body-coverage.json',coverage)
write('provenance.json',{'date':str(datetime.date.today()),'lane':L.name,'counts':[9,39,40],'administrative_context_top_level_keys':list(context),'original_question_bodies':12,'successor_or_version_bodies':5,'all_helpers_guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','limits':{'AS_bytes':512*1024*1024,'sampled_group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'OPENBLAS_NUM_THREADS':1,'OMP_NUM_THREADS':1,'PYTHONDONTWRITEBYTECODE':1},'source_discipline':'Remote body bytes saved before text extraction; access hash checked after extraction and again here. Local history originals and copies hashed before copying/after copying, checked separately in verification. Administrative inputs snapshot only. See failures.md for initial catalogue-read and Google-route deviations.','novelty_status':'No clearance or nomination; current registry heads inaccessible under denied-route policy.','external_writes':False})
(L/'SUMMARY.md').write_text('''# r289 outcome: no nomination

Screened twelve distinct older question families using twelve actual question-posing primary bodies (plus five successor/version bodies). Four families have explicit prior negative/positive resolution statements in retrieved bodies; two are parked campaign duplicates. Remaining families are unqualified rather than advertised as open.

Sustained the poset random-to-random spectral conjecture via promotion/Gram factorization and generalized Coxeter comparison. The first bridge is source-known and insufficient for a gap; the second fails on an exact twelve-state action satisfying the exponent-six relations. Exact rational controls on 206 small nonchain posets found no counterexample. No full source endpoint, PROOF, Lean or manuscript.

Only a provisional shuffle mechanism lead remains; it requires a uniform poset-specific contraction theorem and current prior-art clearance. Counts9/39/next40 unchanged. All outputs are confined to this lane; root alone accepts/counts.

Read SCOUTING.md for statements and dispositions, discovery.md for the two routes, failures.md for candid access/source-discipline deviations. The manifest excludes itself and verification-receipt.json; a separate guarded verification validates hashes, local scientific original/copy bindings and the exact abstract obstruction.
''')
(L/'progress.md').write_text('''# Progress

Administrative instructions, count state, prior campaign context, r288 disposition and seven excluded review questions reconciled. Exact source-ID/author/statement alias screening preceded sustained shuffle work. Older question bodies frozen before extraction; successor bodies compared before the small exact controls. No known-family source was promoted as new. Read scopes, chronology and version limitations are explicit.

Completed: 12-family screen, 12 original bodies, 5 successor/version bodies, two shuffle routes, exact controls, candid failure log and final evidence packet. Incomplete: universal shuffle bound/equality characterization, full mixing endpoint and novelty clearance. No result ready for independent acceptance review; no count change requested.
''')
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
write('manifest.json',manifest)
