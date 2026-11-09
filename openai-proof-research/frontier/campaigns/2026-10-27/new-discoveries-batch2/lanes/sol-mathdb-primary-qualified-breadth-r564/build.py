import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
rows=json.loads((P/'literal-records.json').read_text());ass={}
for line in (P/'assessments.tsv').read_text().splitlines():
 i,d,n=line.split('\t',2);ass[int(i)]=(d,n)
assert len(rows)==len(ass)==50 and set(ass)=={r['mathdb_id'] for r in rows}
out=[]
for r in rows:
 s=r.pop('record');r.update(disposition=ass[r['mathdb_id']][0],technical_assessment=ass[r['mathdb_id']][1],source_url=s['source_url'],title=s['title'],accepted_credit=0,literal_bytes_read=True,complete_mathematical_statement_available=r['mathdb_id']!=344924,current_registry_cleared=False,whole_source_body_read=False,full_dependency_audit=False,primary_passage_read=r['mathdb_id'] in [344583,347690,348215]);out.append(r)
(P/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(P/'proposals.json').write_text('[]\n')
prov=[]
for e in json.loads((P/'downloads.json').read_text()):
 e['coverage']={'korselt':'Definition1.3, final Remark4.6, Conjecture4.7, local Main Theorem proof sentence; portions of Propositions3.1/4.4 visible. Not whole-body/dependency audit. KW undefined in inspected formulation.','recurrence':'Definition Eq1 and factorization Eq13, explicit moments Eq15, identities Eq16, Conjectures1/2 and surrounding comparison. v1 does not contain the identical assigned binomial conjecture; exact later version unbound/unread.','sandpile':'Section6 product definitions, complete Proposition6.1 local proof and Conjecture6.2. Strong product confirmed by worded proposition and diagonal-edge TeX icon. No complete dependency proof replay.'}[e['name']]
 e['whole_body_read']=False;e['closest_successor_body_read']=False;e['full_dependency_audit']=False;prov.append(e)
(P/'source-provenance.json').write_text(json.dumps({'primary_sources':prov,'current_registry':'Unavailable per assignment; HOLD. No absence-of-hits inference.','search':'Three general web queries returned mixed results including MathDB index result, MIT presentation, and ResearchGate snippet. No result opened, no MathDB request made, no snippet used as proof-body evidence. No successor clearance.','extraction':'Stdlib HTMLParser preserves math alttext, includes chrome/script text as inert text, no execution. Derivatives hashed before passage search.'},indent=2)+'\n')
