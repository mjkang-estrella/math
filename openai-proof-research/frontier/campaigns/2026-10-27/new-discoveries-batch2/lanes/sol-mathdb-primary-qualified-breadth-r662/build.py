import json,pathlib,hashlib,collections,itertools,fractions
O=pathlib.Path(__file__).resolve().parent; L=O.parent; I=L/'root-mathdb-breadth-intake-r661'
def write(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def binding(p):
 d=p.read_bytes();return dict(path=str(p.resolve()),sha256=hashlib.sha256(d).hexdigest(),size=len(d))
flat=json.loads((O/'flat-bindings.json').read_text());flat.extend(binding(p) for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md'] if p.exists());write('flat-bindings.json',flat)
records=json.loads((O/'literal-records.json').read_text());rv={}
for line in (O/'reviews.tsv').read_text().splitlines():
 id,c,reason,q,disp,a=line.split('\t');rv[int(id)]=(c,reason,q,disp,a)
assert len(rv)==50
out=[]
for z in records:
 d=z['record'];id=d['mathdb_id'];c,reason,q,disp,a=rv[id]
 out.append(dict(mathdb_id=id,title=d['title'],chunk=z['chunk'],line=z['line'],exact_utf8_statement=d['statement'],statement_utf8_sha256=hashlib.sha256(d['statement'].encode()).hexdigest(),canonical_record_sha256=z['canonical_record_sha256'],source_url=d['source_url'],source_name=d['source_name'],source_version='r301 normalized third-party dated mirror 2026-09-29; primary version unverified except 398958 report 12/2014',completeness_classification=c,completeness_reason=reason,quantifiers=q,disposition=disp,technical_assessment=a,evidence_levels={'literal_statement':'read independently in full','selected_primary_passage':'PDF p78/printed712 read and image checked' if id==398958 else 'not read','whole_source_body':'not read','local_proof':'no full-scope proof claimed','full_dependency':'not audited','successor_proof_bodies':'not read','current_registry':'HOLD unavailable; no requests'},accepted_credit=0,prior_cleared=False,source_scope_cleared=False))
write('dispositions.json',out);write('proposals.json',[])
counts=dict(collections.Counter(z['completeness_classification'] for z in out));write('screening-counts.json',{'literal_reviews':50,'classifications':counts,'proposals':0,'credit':0,'baseline_reported_literal_reviews':7433,'union_if_root_accepts_disjoint_literal_reviews':7483,'full_technical_corpus_coverage':False})
lengths=[]
for w in itertools.permutations([1,2]):
 lengths.append(max(len(s) for k in [1,2] for inds in itertools.combinations(range(2),k) if all((w[inds[j]]>w[inds[j+1]] if j%2==0 else w[inds[j]]<w[inds[j+1]]) and abs(w[inds[j]]-w[inds[j+1]])>=1 for j in range(k-1)) for s in [inds]))
write('bounded-checks.json',{'398953':{'executed':True,'n':2,'k':1,'down_first_lengths':lengths,'average':str(fractions.Fraction(sum(lengths),2)),'displayed_formula':str(fractions.Fraction(5,6)),'limit':'only formula/endpoint correction; credit zero'},'398958':{'executed_calculation':False,'route_screened':'log of matching generating series selects connected incompatibility clusters; union of t edges in an overlap-connected cluster has <=t+1 vertices','stopped':'primary notes explicitly report independent solutions; no certificate or new proof developed'}})
# Read bound administrative material, comparing assigned identifiers and family titles only.
context={}
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 d=json.loads(p.read_text());s=json.dumps(d,ensure_ascii=False);context[p.name]={'assigned_id_text_matches':[id for id in rv if str(id) in s],'bound_before_read':True}
context.update(cayley_decision='Read bound r363 DECISION.md: 364119 source already supplies literal negation; excluded',current_adjudications='Read r661 adjudications and hypothesis queue; 338290/339564/372627 retired,337963 parked;338366 excluded with text/figure reconstruction and unread-journal limitations;338408 parked',ledger_counts='9 additional /39 total /next40; unchanged')
write('context-check.json',context)
write('source-coverage.json',{'literal_records':50,'primary_selected_passages':1,'whole_primary_bodies':0,'successor_bodies':0,'proof_dependency_audits':0,'registry_cleared':0,'398958':{'url':'https://ems.press/content/serial-article-files/46502','version':'Oberwolfach Report12/2014 DOI10.4171/OWR/2014/12','pdf_page':78,'printed_page':712,'coverage':'Wormald statement and all notes read; rendered page verified after binding; adjacent Stanley block incidental to full-page render, not assessed or counted','finding':'Notes explicitly report independent short solutions; no solution bodies supplied or read; no independent proof replay or global priority claim'}})
write('failures.json',{'new_access_failures':[],'upstream_failures_preserved':'r661 failures.json and failed-verifier.py.txt bound, not executed; no upstream verifier run','stopped_routes':['MathDB429: zero requests','proof registry unavailable HOLD','author Gorenstein PDF TLS r642 stopped','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS; ProjectEuclid challenge; ResearchGate403 parked','OEIS A274199/internal403 r542 parked','DOI10.1093/imrn/rnz305 academic.oup.com403 Cloudflare r618 parked'],'restrictions':'No prohibited APIs/browser/TLS bypass, messages or uploads. Only two generic-header EMS fetches; no retries.','screening_limits':['No full source dependency or successor-body clearance','No new substantial hypothesis survived','PDF full-page rendering incidentally includes an adjacent unassigned passage; only Wormald block used; no unrelated record classified'],'deviations':['Initial record display was truncated; all 50 exact statements were subsequently reread in compact complete output before dispositions.']})
summary=f'''# r662 independent breadth handback

Reviewed all 50 assigned literal records, with exact statements, original chunk/line, UTF-8 statement hashes and canonical record hashes. No replacements. Independent completeness: {counts}. Zero proposals and zero discovery credit. Baseline remains 7,433 upstream reported literal reviews; this disjoint lane adds 50 only if root reconciles it (7,483), not full technical corpus coverage. Counts remain 9 additional /39 total /next40.

398958 was the strongest short-route lead. Its primary report 12/2014, PDF p78 / printed712 explicitly records independent short solutions by Gessel, Schaeffer and Stanley. Statement and all notes were read, including a bound rendered page. Solution bodies were not supplied/read; no proof-body or global-priority clearance is claimed. The connected-cluster route was stopped. 398953 has an executed n=2,k=1 mismatch (3/2 versus 5/6), excluded as formula/endpoint correction. 398916 lacks general-point hypotheses; the collinear-point -2 curve is a wording objection only. No substantial proof task is recommended.

Most other rows lack a tractable all-quantifier route or need precise definitions/scope. Known-resolution leads are marked as leads only, without pretending to read their bodies. One selected primary passage, zero whole bodies, zero successor bodies, zero full dependency audits, registry HOLD. No MathDB requests or retries of parked routes. Two lawful EMS primary fetches used generic headers; bytes bound before extraction and derivatives before reading. No new access failures.

Independent verification checks intake exact payload, all 38 original/copy pairs, original r301 inventory against intake binding, all 20 chunks in place and all 8 frozen inputs separately, 7,433 coverage keys, three mutually disjoint reserved sets and protected IDs, all literal/canonical hashes and lane exact payload. No upstream verify.py executed. Flat references only; no corpus copies. Integrity PASS is not mathematical/novelty PASS. Runnable verification: `bash verify.sh` from this lane; verifier is read-only. Final receipt records bounded hash, size and extra-file negative tests using temporary synthetic fixtures, without original mutations.

r304 exclusions and history and r363 Cayley decision remain operative; r661 adjudications unchanged. 338366 credit exclusion retains text/figure reconstruction and unread-journal caveats; 338408 and337963 parked;338290/339564/372627 retired. Claude r628 held untouched and uncounted, Sol r660 untouched. No shared ledger, Lean, manuscript, git, or credit changes.
'''
(O/'SUMMARY.md').write_text(summary)
print(counts)
