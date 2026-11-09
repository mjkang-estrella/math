import pathlib,json,hashlib,collections,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r657'
def write(n,d): (O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def binding(p):
 d=p.read_bytes();return dict(path=str(p.resolve()),sha256=hashlib.sha256(d).hexdigest(),size=len(d))
refs=json.loads((O/'flat-bindings.json').read_text());refs += [binding(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')]
refs += [binding(p) for p in [L.parent/'../../../../AGENTS.md'] if p.exists()]
# Bind the local extracted records explicitly; originals were bound before extraction.
write('literal-binding.json',binding(O/'literal-records.json'))
rows={int(a):(b,c,d,e) for a,b,c,d,e in (s.split('\t') for s in (O/'reviews.tsv').read_text().splitlines())};literals=json.loads((O/'literal-records.json').read_text());out=[]
for x in literals:
 r=x['record'];c,reason,disp,assessment=rows[r['mathdb_id']]
 out.append({'mathdb_id':r['mathdb_id'],'title':r['title'],'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'corpus_path':x['corpus_path'],'corpus_line':x['line'],'source_url':r['source_url'],'source_version':r['source_name'],'completeness':{'classification':c,'reason':reason,'independent':True},'quantifier_scope':r['statement'],'technical_assessment':assessment,'disposition':disp,'accepted_credit':0,'evidence':{'literal_statement_read':True,'primary_passage_read':r['mathdb_id'] in [397960,397962],'whole_source_body_read':False,'selected_contribution_body_read':r['mathdb_id'] in [397960,397962],'full_proof_dependency_audit':False,'successor_body_clearance':False,'current_registry_clearance':False}})
write('dispositions.json',out);write('proposals.json',[])
write('screening-counts.json',{'literal_reviews':50,'classification_counts':dict(collections.Counter(x['completeness']['classification'] for x in out)),'proposals':0,'credit':0,'baseline_literal_reviews':7333,'prospective_total_if_root_reconciles':7383})
# Bind direct contexts and mechanically inspect only assignment intersections.
res=json.loads((I/'reserved-ids-r658.json').read_text());ids=set(res['ids']);cov=json.loads((I/'coverage-delta.json').read_text());active=json.loads((I/'active-breadth-reservations.json').read_text());assert len(cov)==7333;assert not ids&set(map(int,cov));assert not ids&set(res['protected_ids'])
for j,a in enumerate(active):
 assert not set(a['ids'])&set(map(int,cov));assert not set(a['ids'])&set(a['protected_ids'])
 for b in active[j+1:]:assert not set(a['ids'])&set(b['ids'])
# r304 lists are bound and parsed; no promoted target and no accepted family credit.
contexts={}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;d=json.loads(p.read_text());text=json.dumps(d);contexts[name]={'assigned_numeric_id_mentions':[v for v in sorted(ids) if str(v) in text],'top_level_keys':list(d)}
write('context-check.json',{'baseline':len(cov),'reserved_sets':[{'lane':a['lane'],'count':len(a['ids']),'status':a['status']} for a in active],'pairwise_disjoint':True,'coverage_disjoint':True,'protected_disjoint':True,'r304':contexts,'cayley_decision_read':True,'r657_adjudications_read':True,'ledger_counts':{'additional':9,'total':39,'next':40},'promotions':0})
# Deduplicate flat references, preserving originals in place.
write('flat-bindings.json',list({r['path']:r for r in refs}.values()))
write('source-coverage.json',{'selected_ids':[397960,397962],'source':'OWR 2012/40 DOI10.4171/OWR/2012/40','read_text_lines_1_based':[1210,1334],'printed_pages':'2453-2456','visual_page':{'pdf_page':26,'printed_page':2454},'coverage':'Entire Kaplan contribution from introductory quadratic form to final proof-outline paragraph and references; Theorem4 and Corollary1 exact statements; proof outline read, not a complete proof/dependency audit. Other contributions and successor bodies not cleared.','registry':'unavailable HOLD; zero MathDB requests','successor':'No successor search undertaken after direct cited-source theorem/corollary defeated eligibility.'})
write('selected-passages.json',[{'mathdb_id':397960,'location':'p2454 Theorem4; form defined p2453','bridge':'Same n>=1 excluding1,2,3,6, same residues j/5, ratio<=2 and Q5=n; literal direct theorem match.','proof_coverage':'weighted-theta/Deligne/finite-exception outline pp2455-2456 read; underlying modular forms and computations not replayed.'},{'mathdb_id':397962,'location':'p2455 Corollary1; definitions p2454','bridge':'Both n>=6 semigroup and partition conclusions printed; weight/genus and hook conditions supplied in contribution.','proof_coverage':'Reduction via Apery set and theorem outline read; not a complete dependency audit.'}])
write('bounded-checks.json',{'executed':'No new mathematical enumeration: direct all-quantifier source-statement comparison is decisive for two source exclusions.','planned':'None; no substantial hypothesis survives screening.','scope_limit':'No inference from finite tests or tags/status/solution count.'})
write('failures.json',{'new_http_failures':[],'restrictions_preserved':['MathDB429 zero requests','Google/GitHub APIs/raw/codeload/diff and ScienceDirect unused','author Gorenstein PDF TLS r642 stopped','OEIS A274199/internal403 r542 stopped','OUP DOI10.1093/imrn/rnz305 Cloudflare403 r618 stopped','AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403 parked','current registry unavailable HOLD'],'credit_restrictions':['338366 excluded: published object reconstructed modulo text/figure defects, journal bodies unread; no named prior refutation claimed','338408 parked;338290/339564/372627 retired;337963 parked'],'deviations':['Local literal-records.json was generated from pre-bound originals and then displayed before its own separate file hash/size binding. Canonical record hashes were generated at extraction; later literal-binding.json does not retroactively repair the derivative timing deviation. No unbound original scientific records were consulted.'],'stopped_routes':['No further source hunt after exact cited source already printed theorem and corollary.'],'failed_checks':[]})
print((O/'screening-counts.json').read_text())
