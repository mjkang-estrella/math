import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
notes={int(i):(s,t) for i,s,t in (x.split('\t',2) for x in (O/'assessment.tsv').read_text().splitlines())}
rows=json.loads((O/'assigned-records.json').read_text());out=[]
for a in rows:
 r=a['record'];i=r['mathdb_id'];status,note=notes[i];p=O/'sources'/(r['source_url'].rsplit('/',1)[-1]+'.txt')
 out.append({'mathdb_id':i,'original_literal_statement':r['statement'],'original_chunk':a['original_chunk'],'original_line':a['original_line'],'statement_utf8_sha256':sha(r['statement'].encode()),'canonical_record_sha256':sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'canonical_url':r['canonical_url'],'primary_url':r['source_url'],'disposition':status,'technical_disposition':note,'evidence_levels':{'literal_statement':'all quantifiers read','primary':'selected passages; downloaded whole PDF is not whole-body review','primary_text':str(p),'proof_body':'selected source/successor proof passages only' if i in [341050,341926,342106,342260,341395,341477] else 'not audited','dependencies':'not independently audited','current_registry':'HOLD; not cleared'},'duplicate_prior_status':'published bridge/refutation or wording correction; no credit' if status.startswith('RETIRE') else 'unresolved bounded prior-art coverage; no novelty assertion','accepted_credit':0})
assert len(out)==50 and set(notes)=={r['mathdb_id'] for r in out}
(O/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
(O/'proposals.json').write_text(json.dumps({'qualified_briefs':[],'accepted_credit':0,'reason':'No row has both a tractable full-scope mechanism and completed primary/successor/prior qualification. No complete candidate proposed.'},indent=2))
(O/'coverage.json').write_text(json.dumps({'baseline_reported_literal_reviews':3333,'own_literal_reviews':50,'own_reservation_only':True,'proposed_reported_union':3383,'shared_ledger_changed':False,'distinct_primary_pdfs_received':48,'successor_pdfs_received':2,'whole_body_reviews':0,'dependency_audits':0,'registry_clearances':0,'qualified_briefs':0,'accepted_credit':0,'campaign_counts':{'additional':9,'total':39,'next':40},'limits':'Selected passages are uneven: some exact statements, some adjacent discussion/definitions. Not fifty full primary proof audits.'},indent=2))
