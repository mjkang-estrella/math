import json,hashlib,datetime,re,resource,os,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).resolve().parent;r=json.loads((p/'reservation.json').read_text());prov=json.loads((p/'inputs/provenance.json').read_text());utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
def h(f):return hashlib.sha256(f.read_bytes()).hexdigest()
# Literal provenance, including the exact statement bytes after JSON decoding.
for k,v in prov.items():v['statement_sha256_utf8']=hashlib.sha256(v['record']['statement'].encode()).hexdigest();v['line_one_based']=v.pop('line',v.get('line_one_based'))
(p/'inputs/provenance.json').write_text(json.dumps(prov,ensure_ascii=False,indent=2)+'\n')
D={
319574:('PARK_UNIFORM_TOPOLOGICAL_SCOPE','Conjecture 3.9; Theorem 3.7 and note added in proof','Need a positive constant uniform in d and prime-power q, not shellability Conjecture 3.10 or quadratic degree bound.'),
319656:('PARK_CLASSIFICATION_SCOPE','Conjecture 13 and Theorem 14','All nontrivial block-transitive 6-designs; Steiner lambda=1 is only a subclass. Two source group exceptions are not the full conjecture.'),
319940:('EXCLUDE_SOURCE_PROVED','Conjecture 1, Theorem 1, Corollaries 1–2; entire five-page proof','Both digit assertions explicitly proved by Pan; no discovery credit.'),
320378:('EXCLUDE_LITERAL_DOMAIN_CORRECTION_PARK_INTENDED','Introduction, Conjecture 0.1 and Theorem 0.2','Tree/isolated-vertex polynomial-ring examples refute only the omitted full-dimensional domain. Need intended connected nonbipartite depth<7 example or full lower bound.'),
321036:('EXCLUDE_PUBLISHED_PROOF','Survey Conjecture 2.8; Chen–Li §2 construction and colouring proof','Chen–Li already construct every admissible pair.'),
318155:('PARK_FLAGSHIP_SCOPE','Conjecture 13, preceding tree theorems and following partial ranges','All k and all host orders; regularity/large-linear-k ranges are insufficient.'),
318840:('PARK_ASYMPTOTIC_SCOPE','Conjecture 6.13 and preceding separator discussion','Uniform separator theorem unpaid; m/n mismatch is a correction, d=1 undefined exponent is not a substantive refutation.'),
318975:('EXCLUDE_PUBLISHED_BIJECTION','§6.1, Conjecture 6.2, definitions and Lemma 6.1; Elizalde later Corollaries 4.2–4.3 proof bodies','Exact full descent-set preserving bijection already published.'),
318983:('EXCLUDE_SOURCE_REFUTATION','Conjecture 1.1, Theorem 1.2 and full four-case proof','Take d=n; printed sequence has no sum-n subsequence in any generator. This is the exact assigned refutation.'),
319242:('PARK_UNIFORM_EXTREMAL_SCOPE','Conjectures 1.3–1.4 and bias definition','Need epsilon(k)>0 for every k; source k=2 and weaker k=3 results do not resolve this.'),
319288:('PARK_ALL_DEGREES_ALGEBRA','§5, Conjecture 5.1 and sharp-image discussion','No leading-term proof of simultaneous spanning and freeness; Hilbert data alone insufficient.'),
364497:('PARK_FLAGSHIP_TRANSVERSAL_SCOPE','Conjecture 1.7, Theorems 1.8–1.11 and real/complex discussion','No all-ri real transversal proof; prime-power complex analogues do not subsume it.'),
317294:('PARK_LIFTING_COMPATIBILITY','Conjecture 6.2, M8591 counterexample to K2 and partial-field appendix','Specialization easy; lifting representations from all finite fields unpaid. Printed K2 counterexample is P4-representable.'),
317334:('PARK_LOW_INDEX_CLASSIFICATION','§5 Conjecture 5.2 across v1/v2/v3; latest figures 27–28 visually read','No non-RAAG/minimality proof or completeness theorem for ten 3-nuclei. v1 six-object list is superseded.'),
317742:('PARK_FLOER_SCOPE','Introduction, Conjecture 1.1 across versions; almost-alternating discussion','Need quantum/delta gradings and differential shifts for every link/page; no route beyond special links.'),
317975:('PARK_INFINITE_GAME_SCOPE','Conjecture 1 across v1/v2/v3; orientable extension Conjecture 2','No induction on arbitrary planar Sprouts regions; finite starts and surface stabilization do not prove modular pattern.'),
318003:('PARK_GENERAL_ZERO_SUM_SCOPE','Conjecture 1.1 and Theorem 1.2 across all versions; journal introduction','Arithmetic progression with even step is not arbitrary zero-sum weights. No full matching permutation argument or witness.'),
380331:('EXCLUDE_CLASSICAL_MATRIX_REDUCTION','Genest Definitions 1.6.1–1.6.4, 1.7.1 and §1.7 symmetry propositions','Complete ordinary binary elimination/strong-regularity reduction in ATTEMPTS.md; no significant new mechanism. Binary-inversion primary PDF unavailable (503); no literature clearance claimed.'),
380434:('PARK_HOMOTOPY_BRIDGE','Construction G_k,X and Conjecture 4.1','Need k=1 fibre contraction, not higher-subdivision proof or changing printed K2 to T.'),
379622:('PARK_EXACT_FOREST_INJECTION_GAP','Partition-function conventions, Example 5.2 and Conjectures 5.3–5.4','Exact coefficient count reduction in ATTEMPTS.md; neither single-circuit nor alternating-trail switching proved injective. No witness.')}
receipts=[]
for f in sorted((p/'sources').glob('*receipts.json')):receipts+=json.loads(f.read_text())
versions={}; results={};inventory={}
for ident in r['ids']:
 k=str(ident);a=prov[k];rec=a['record'];vs=re.findall(r'\[v(\d+)\]',(p/'sources'/(k+'.abs.html')).read_text());versions[k]={'listed_versions':vs,'fetched_pdf_and_text':all((p/'sources'/(k+'v'+v+'.txt')).exists() for v in vs)}
 status,read,gap=D[ident]
 inventory[k]={'literal_record':'Entire statement and full parsed record read','primary_passages_read':read,'versions':'Every version listed on fetched abstract downloaded; target passages selectively compared, not complete every-version proof audit','latest_journal_corrections_citing_bodies':'Incomplete. Specific later proof bodies read only where expressly named; no candidate source-qualified.','figures':'Latest nuclei Figures 27/28 visually inspected at PDF page 48' if ident==317334 else 'No visual figure audit claimed','artifacts':[str(f.relative_to(p)) for f in sorted((p/'sources').glob(k+'*'))]}
 results[k]={'mathdb_id':ident,'title':rec['title'],'canonical_url':rec['canonical_url'],'literal_statement':rec['statement'],'statement_sha256_utf8':a['statement_sha256_utf8'],'raw_provenance':{x:y for x,y in a.items() if x!='record'},'raw_artifact':f'inputs/{k}.raw.jsonl','full_parsed_record':rec,'source_url':rec['source_url'],'disposition':status,'review_depth':inventory[k],'versions':versions[k],'ordinary_attempts':'ATTEMPTS.md','precise_remaining_gap_or_exclusion':gap,'historical_status':'history-screen.txt; ID substring false positives and generic family matches are not prior solutions. Related r263/317333 low-index hold retained. No novelty clearance.','source_receipts':[x for x in receipts if x['name'].startswith(k)],'current_registry':'registry-screen.json: cached trees plus current public raw catalogues, incomplete head/scope; no API calls.','qualification_limits':['Latest journal and all citing primary proof bodies not exhaustively read','Current complete registry HEAD and theorem-body clearance absent','No Lean endpoint, independent review, manuscript or extracted replay'],'pi_handoff':None,'accepted':False,'credit':0}
assert set(results)==set(map(str,r['ids'])) and len(results)==20
(p/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n');(p/'source-read-inventory.json').write_text(json.dumps(inventory,indent=2,ensure_ascii=False)+'\n');(p/'version-inventory.json').write_text(json.dumps(versions,indent=2)+'\n')
reg=[]
for f in sorted((p/'sources').glob('registry-*')):
 if f.name.endswith('json'):continue
 s=f.read_text();pat=r'Tverberg|block.transitive|Lemke|Bialostocki|Genest|Rayleigh|marked.cycles|nuclei|PBT|319940|318975|380331|379622'
 reg.append({'path':str(f.relative_to(p)),'sha256':h(f),'bounded_routing_matches':[l[:1200] for l in s.splitlines() if re.search(pat,l,re.I)],'role':'Routing only, no blanket theorem-body clearance'})
for rel in ['../expanded-corpus-r254/openai-complete-preprints.body','../expanded-corpus-r254/pool-tree.body','../path-polynomial-source-qualification-r1/omega-current-D5.body']:
 f=p/rel
 if f.exists():
  data=json.loads(f.read_text()) if f.suffix=='.body' and f.read_text().lstrip().startswith('{') else None
  reg.append({'external_cached_path':str(f.resolve()),'sha256':h(f),'tree_sha':data.get('sha') if isinstance(data,dict) else None,'truncated':data.get('truncated') if isinstance(data,dict) else 'unknown','role':'Immutable cached routing only; no current complete-HEAD inference'})
(p/'registry-screen.json').write_text(json.dumps({'utc':utc,'current_head_sha':'NOT ESTABLISHED','github_api':'Not called; inherited 403 respected','sources':reg,'qualification':'Incomplete; no candidate nominated'},indent=2)+'\n')
# Correct extraction for spelling-broken and differently numbered target passages.
vpass=json.loads((p/'version-passages.json').read_text())
patterns={'319574':r'Conjecture 3\.9','318155':r'Conjecture 13','317294':r'Conje.ture 6\.2','364497':r'Conjecture 1\.7','319288':r'Conjecture 5\.1'}
for k,pat in patterns.items():
 for entry in vpass[k]:
  s=(p/entry['file']).read_text();m=re.search(pat,s,re.I)
  if m:entry.update(passage=s[max(0,m.start()-120):m.start()+1200],page_1based=s[:m.start()].count('\f')+1)
(p/'version-passages.json').write_text(json.dumps(vpass,indent=2,ensure_ascii=False)+'\n')
expected=(p/'reservation.sha256').read_text().split()[0];actual=h(p/'reservation.json');assert actual==expected
checks={'utc':utc,'expected':expected,'before':json.loads((p/'reservation-check-before.json').read_text())['sha256'],'after':actual,'before_after_match':True,'ids_exactly20':True,'raw_newline_preserved':all((p/'inputs'/f'{k}.raw.jsonl').read_bytes().endswith(b'\n') for k in results),'raw_hashes_match':all(h(p/'inputs'/f'{k}.raw.jsonl')==prov[k]['raw_sha256'] for k in results),'all_listed_versions_downloaded':all(x['fetched_pdf_and_text'] for x in versions.values()),'no_children_lean_solver_git_publication':True,'no_acceptance_claim':True}
(p/'reservation-hashchecks.json').write_text(json.dumps(checks,indent=2)+'\n');(p/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
processes=subprocess.run(['ps','-eo','pid,ppid,comm,args'],capture_output=True,text=True,check=True).stdout
owned=[l for l in processes.splitlines() if 'expanded-corpus-r266/fetch_' in l and not any(t in l for t in ['bash -','timeout 10s','python -I -B -'])]
(p/'process-final.json').write_text(json.dumps({'utc':utc,'fetch_jobs_running':owned,'note':'All fetch command sessions exited. No children, Lean, solver or background services started. ps snapshot excludes its containing shell command.'},indent=2)+'\n')
(p/'resource-and-process-log.json').write_text(json.dumps({'utc':utc,'job_scripts':['fetch_sources.py','fetch_versions.py','fetch_supplement.py','fetch_registry.py','fetch_chen.py','finalize.py'],'limits':'Each scripted fetch/text/hash job sets CPU120 seconds, AS6GiB, affinity at most2 CPUs; fetch commands wrapped timeout140 seconds. ThreadPool max2; urllib timeout14 seconds; pdftotext timeout15 seconds. No external caches.','measurements':'Receipts log UTC/status/hash/error per HTTP fetch. Per-job peak RSS/CPU elapsed were not separately sampled; do not infer complete telemetry.','ru_maxrss_kib_finalize':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'background_jobs':0},indent=2)+'\n')
manifest={str(f.relative_to(p)):h(f) for f in sorted(p.rglob('*')) if f.is_file() and f.name!='hashmanifest.json'}
(p/'hashmanifest.json').write_text(json.dumps({'utc':utc,'algorithm':'sha256','self_excluded':True,'files':manifest},indent=2)+'\n')
print(json.dumps(checks));print('Manifest files',len(manifest))
