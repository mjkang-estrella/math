import json,pathlib,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
def save(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
rows=json.loads((P/'literal-records.json').read_text());notes={}
for line in (P/'notes.tsv').read_text().splitlines():
 i,scope,status,note=line.split('\t');notes[int(i)]=(scope,status,note)
assert len(notes)==50
passages={398790:('12861',2550,2602,'pp61-62: complete short talk read; algorithm outline, no complete dependency proof'),398936:('12872',418,525,'pp646-648: talk read, figure not interpreted; KP recurrence versus requested bijection'),398948:('12872',2872,2926,'pp696-697: second tidbit read including statement and proof outline'),399008:('12975',1722,1770,'p1013: statement and rank/CD results read; remainder of talk not fully read'),399079:('12983',123,155,'p1369: complete short talk read; announced counterexamples, construction in cited article not read'),400382:('14741',626,818,'pp1890-1893: complete Plonka talk read; AAK theorem, Theorem2 proof and algorithm'),400383:('14741',626,818,'same complete talk as400382')}
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];scope,status,note=notes[i];s=r['statement']
 o=dict(mathdb_id=i,title=r['title'],statement=s,statement_utf8_sha256=hashlib.sha256(s.encode()).hexdigest(),canonical_record_sha256=x['canonical_record_sha256'],corpus_chunk=x['chunk'],corpus_line=x['line'],source_url=r['source_url'],source_name=r['source_name'],disposition=status,technical_disposition=note,accepted_credit=0,proposal=False,
 scope_flags=dict(literal_record_statement_read_in_full=True,mathematical_statement_self_contained=scope=='full',record_metadata_full_label_not_relied_on=True,primary_selected_passage_read=i in passages,whole_source_volume_read=False,successor_proof_body_read=False,local_proof_established=False,full_dependency_audit=False,current_registry_cleared=False,novelty_cleared=False,full_scope_resolution_claimed=False),
 primary_coverage=dict(file='ems-'+passages[i][0]+'.body.txt',line_start=passages[i][1],line_end=passages[i][2],coverage=passages[i][3]) if i in passages else None,registry='HOLD: unavailable; zero MathDB requests',successor='not inspected; no absence-of-hits inference')
 out.append(o)
save('dispositions.json',out);save('proposals.json',[])
save('source-coverage.json',dict(literal_record_reviews=50,self_contained_records=sum(o['scope_flags']['mathematical_statement_self_contained'] for o in out),primary_selected_passages=7,distinct_primary_talks=6,whole_report_volumes=0,successor_bodies=0,complete_dependency_audits=0,registry_cleared=0,primary_ids=list(passages),pdf_visual_review=False,pdf_limit='Textual theorem and definition passages only; no diagram-dependent deduction. PDF/text hashes persisted before extraction/read.',search='One public web search batch surfaced planar-morph theorem and Vogel leads. Search snippets used only as leads; eligibility dispositions use retained primary passages. ScienceDirect and ResearchGate search results not opened.',bounded_calculations='One exact rational Hankel perturbation test for two overlapping records; no proof/novelty PASS'))
save('failures.json',[
 dict(kind='initial_instruction_path',detail='First cat used campaign path without openai-proof-research prefix; failed, then corrected before content review.'),
 dict(kind='verifier_development',detail='First reservation assertion double-counted own assignment already present in active-breadth-reservations; diagnostic run showed exact same fifty, then unique own-set check corrected. Neither upstream nor reservations modified.'),
 dict(kind='coverage_limit',detail='Initial combined record display truncated; dedicated show.py output recovered all missing statements398936..399440. Fifty literal statements read; not fifty primary/full-dependency reviews.'),
 dict(kind='parked_inherited',detail='MathDB429; AIM/Kourovka/EGRES/AIProofWatch; DMGT TLS; ProjectEuclid challenge; ResearchGate403; OEIS A274199/internal403; r578 arXiv coloringHTML404, author certificate failure and Christensen-Hovey timeout; no retry/bypass.'),
 dict(kind='registry',detail='Current proof registry unavailable. All novelty gates HOLD.'),
 dict(kind='new_fetch_failures',detail='None: five EMS landing HTML and five primary report PDFs fetched lawfully; no prohibited API/browser use.'),
 dict(kind='scope',detail='No promotion; source-reported solution is explicitly separated from independently replayed proof. No focused task/count changes. Prior incomplete344924,386396,387650 and all protected adjudications preserved outside assignment.')
])
(P/'SUMMARY.md').write_text("""# r590 qualified breadth screening

Exactly fifty assigned literal MathDB RECORD statements read, with individual quantifier-aware technical dispositions, exact UTF-8 statement hashes, canonical record hashes and original corpus chunk/line. Baseline remains 5,683 reported record reviews; this packet offers fifty disjoint additional record reviews for root reconciliation, not complete mathematical corpus coverage. Shared coverage and counts were not edited. Counts remain 9 additional / 39 total / next 40.

**Zero proposals and zero discovery credit.** Seven rows received selected primary-passage review (six distinct talks in five report volumes), including definitions and the stated source-internal results. No entire report-volume audit, successor proof-body audit, complete dependency audit, registry clearance or novelty PASS is claimed. Several other records explicitly report established results; those have HOLD source/eligibility dispositions rather than invented open targets.

The primary reports already announce the polynomial planar morph, prove the compatible-family count by a distributive-lattice outline, report the solved two-variable autoregressive problem, and announce Poisson-equivalence counterexamples. The map-counting report distinguishes its recurrence derivation from the still-desired bijection. The exponential-sum report gives AAK thresholds and an algorithm. A bounded exact rational calculation verifies a positive error floor for shortening a two-exponential signal at tolerance1/1000; this is only a wording/domain obstruction shared by400382/400383 and receives no credit.

Integrity: independent checks of intake exact payload, all44 original/copy pairs, all20 original r301 chunks in place and all8 frozen_inputs; no corpus/historical-tree copies. All active reservation sets are pairwise disjoint and avoid coverage/protected IDs. Solr588 and Claude r504 reservations untouched. r304 exclusions/historical dispositions, r363 Cayley decision and current r589 adjudications bound before consultation; no protected or carried-incomplete judgment changed.

Access: zero MathDB requests; blocked routes remain parked; ten successful EMS requests only plus one public web-search batch. No accounts, messages, uploads, browser, GitHub/Google API, ScienceDirect, TLS bypass, Lean, manuscripts, shared ledger or git actions. All helper Python used the fixed guard with unchanged512MiB/CPU210/wall230 limits and required environment. Standard-library HTMLParser used. Raw PDF hashes persisted before extraction; derivative hashes persisted before searching. PDF work was read-only text inspection under the PDF skill, without figure-dependent claims.

Run the read-only verifier via the fixed helper guard and python3 -B verify.py. It returns nonzero on any mismatch and writes nothing. Negative tests cover same-size hash mutation, size mutation and extra-file injection in memory, leaving originals unchanged. Integrity PASS is independent of mathematical or novelty acceptance. See final-verification-receipt.json and manifest.json for exact sealed payload identity.
""")
