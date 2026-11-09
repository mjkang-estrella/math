import pathlib,json,hashlib,collections,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent
def load(p):return json.loads(p.read_text())
def put(name,d):(P/name).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
rows={int(x.split('|')[0]):x.split('|') for x in (P/'assessments.tsv').read_text().splitlines()};lit=load(P/'literal-records.json');assert len(rows)==len(lit)==50
sources={360288:[('2310.06192v1.txt',[(72,81),(768,787)]),('2310.06192v2.txt',[(829,836)])],360607:[('2311.01208v1.txt',[(1056,1123),(1143,1164)]),('2311.01208v2.txt',[(60,78),(1062,1091)])],361612:[('2401.14301v1.txt',[(740,752)]),('2401.14301v5.txt',[(1533,1580)])],361613:[('2401.14301v1.txt',[(753,760)]),('2401.14301v5.txt',[(1581,1590)])],361981:[('2402.14661v1.txt',[(355,362)]),('2402.14661v2.txt',[(373,381)])]}
disp=[]
for e in lit:
 r=e['record'];i=r['mathdb_id'];_,cl,quant,reason,status,assessment=rows[i]
 disp.append({'mathdb_id':i,'title':r['title'],'corpus_chunk':e['chunk'],'corpus_line':e['line'],'canonical_record_sha256':e['canonical_record_sha256'],'exact_utf8_statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'classification':cl,'classification_reason':reason,'quantifiers':quant,'disposition':status,'technical_assessment':assessment,'source_url':r['source_url'],'source_coverage':sources.get(i,[]),'primary_passage_read':i in sources,'whole_primary_body_read':False,'local_full_scope_proof':False,'full_dependency_audit':False,'current_registry_cleared':False,'novelty_cleared':False,'accepted_credit':0,'remaining_obligations':'Exact source definitions and full-scope route; applicable source/successor proof-body and dependency audit; current public registry and independent eligibility review. No hypothesis recommended.'})
put('dispositions.json',disp);put('proposals.json',[])
put('source-coverage.json',{'literal_records':50,'primary_and_successor_selected_passage_ids':sorted(sources),'whole_primary_bodies':0,'whole_successor_bodies':0,'full_dependency_audits':0,'registry':'unavailable HOLD; zero MathDB requests','selected_passages':sources,'search_limit':'Text searches served as routing only; no abstract/search match is proof clearance. External closest-successor journal bodies not searched or audited; latest arXiv versions only.','calculations':'Exact arithmetic instances in calculations.json; no full-scope mathematical outcome.'})
# Flat references: bind existing administrative contexts and guard/required rules without copying trees.
refs=load(P/'flat-bindings.json')
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md']:
 if p.exists() and str(p) not in {x['path'] for x in refs}:
  b=p.read_bytes();refs.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
put('flat-bindings.json',refs)
ids={d['mathdb_id'] for d in disp};acc=load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=load(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
def matching(x):
 if isinstance(x,dict):
  found=[]
  if x.get('mathdb_id') in ids or ids&set(x.get('mathdb_ids',[])):found.append(x)
  else:
   for v in x.values():found+=matching(v)
  return found
 if isinstance(x,list):return sum((matching(y) for y in x),[])
 return []
put('context-screen.json',{'r304_assigned_id_matches':matching(acc)+matching(hist),'accepted_family_count':acc['accepted_family_count'],'cayley_decision_read':True,'r711_adjudications_read':True,'credit_baseline':'9 additional /39 total /next40; unchanged','note':'ID matching is only an administrative exclusion screen, not a family-equivalence or prior-proof clearance; no promotions.'})
put('failures.json',{'fetch_failures':[e for f in ['source-provenance.json','successor-provenance.json'] for e in load(P/f) if 'failure' in e],'preserved_stopped_routes':['MathDB HTTP429; zero requests','r578 arxiv/html/2207.02920v2 HTTP404; Torontomu Erdos-Gyarfas PDF TLS; Rochester Christensen-Hovey timeout','r642 author Gorenstein PDF TLS failure','r684 arxiv/html/2201.12415v2 and arxiv/pdf/2201.12415v2 HTTP404','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS','ProjectEuclid challenge','ResearchGate HTTP403','OEIS A274199/internal HTTP403 r542','DOI10.1093/imrn/rnz305 academic.oup.com HTTP403 Cloudflare r618'],'deviations':['Schema inspection printed administrative coverage keys/sample entries before binding; no scientific records read then. This ordering deviation is retained and not retroactively cured.','First literal print was truncated; selected statement-only ranges were subsequently read to cover all50 completely.','Source routing searches emitted adjacent unassigned source conjecture/theorem hits; not counted as reviews. Curated coverage is limited to assigned passages.'],'limitations':['No current proof registry clearance; no absence-of-hits inference.','No full-source or full-dependency audit; integrity PASS is not mathematics or novelty PASS.','338366 remains excluded with explicit text/figure reconstruction defects and unread-journal limitations.','No shared edits, no git, no children, no Lean/manuscript/credit changes; r710 and held r628 reservations untouched.']})
counts=collections.Counter(d['classification'] for d in disp)
(P/'SUMMARY.md').write_text('''# r712 breadth handback

Exactly 50 assigned literal records reviewed, no replacements; 0 hypothesis briefs, 0 discovery credit. This adds 50 literal statement reviews to baseline 8,683 (prospective reconciled total 8,733), not full technical corpus coverage. The 10,000 routing rows remain metadata only. Root must reconcile; shared coverage was not edited.

Classification counts: '''+', '.join(f'{k}: {v}' for k,v in sorted(counts.items()))+'''. Exact UTF-8 statements, canonical record hashes, chunk/line, quantifiers and individual reasons are in dispositions.json. Missing-scope rows remain present.

Integrity checks independently passed the exact r711 payload, 46 direct original/copy pairs, r301 manifest binding, all 20 original chunks in place, 8 separately listed frozen inputs and three disjoint 50-ID reservations against 8,683 coverage and protected IDs. No upstream verifier executed. r710 and rate-limit-held r628 remain reserved. No focused hypothesis active.

Selected primary and latest arXiv passages cover five records across four papers: cube stacking (v1/v2), Riemann sums (v1/v2), Sun determinants (v1/v5), quandle enhancement (v1/v2). No whole-body or full-dependency clearance. Riemann Conjecture3.2 remains outside the adjacent proved ranges in both versions; literal prose claiming subsequent resolution is not relied on. Cube v2 Conjecture28 retains the uniform level-construction obstruction. Sun v5 retains Conjectures6.4/6.5; skew-symmetry proves squareness only. Quandle v2 Conjecture4.2 repeats the arbitrary-cocycle scope issue; no wording correction proposed for credit.

Executed exact rational checks show opposite consecutive-difference signs for left sums at b=3/4 and right sums at b=5/4; n<=40 checks at b=7/4 fit the conjectured directions but prove no universal assertion. Sun p=5 gives determinant729, root27, and matching character -1. These are uncredited instances. No finite search is promoted to a full-scope route.

All source bytes were bound before extraction and derivatives before content search. Exact URLs, versions, UTC and hashes appear in source-provenance.json and successor-provenance.json. Current proof registry unavailable: HOLD. No source/novelty/math PASS inferred from hashes or metadata. No new HTTP fetch failed; inherited stopped routes remain parked. Disclosed administrative bind-order and broad routing-output deviations are in failures.json.

Read-only verification: run python3 -B verify.py through the fixed helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. The verifier checks actual originals, reservations, all literal/canonical hashes, source bindings and exact lane payload; mismatches exit nonzero. Negative rejection tests and separate final receipt are retained. Manifest excludes only itself and final-verification-receipt.json. No Lean, manuscript, shared ledger or credit changes. Campaign stays 9 additional /39 total /next40.
''')
print(dict(counts))
