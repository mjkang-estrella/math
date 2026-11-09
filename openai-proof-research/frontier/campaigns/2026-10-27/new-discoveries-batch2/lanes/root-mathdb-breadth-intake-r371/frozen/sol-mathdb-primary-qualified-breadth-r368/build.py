from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent
h=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(R/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
xs=json.loads((R/'records.json').read_text());notes={}
for ln in (R/'disposition-notes.tsv').read_text().splitlines():
 n,d,r=ln.split('\t');notes[n]=(d,r)
assert len(notes)==50 and set(notes)=={str(x['mathdb_id']) for x in xs}
refs={}
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').iterdir()):
 for i,line in enumerate(p.open(),1):
  x=json.loads(line);n=str(x['mathdb_id'])
  if n in notes:refs[n]={'path':str(p.resolve()),'line':i,'record_canonical_json_sha256':h(json.dumps(x,sort_keys=True,ensure_ascii=False).encode())}
rows=[]
for i,x in enumerate(xs):
 n=str(x['mathdb_id']);d,r=notes[n];hay=6<=i<=15;succ=n in ['388030','388035']
 rows.append({'mathdb_id':x['mathdb_id'],'title':x['title'],'canonical_url':x['canonical_url'],'source_url':x['source_url'],'literal_statement':x['statement'],'statement_sha256':h(x['statement'].encode()),'record_ref':refs[n],'disposition':d,'reason':r,'credit':0,'record_statement_review':True,'primary_statement_review':hay,'primary_body_review':hay,'successor_body_review':succ,'proof_section_review':succ,'concluding_proof_section_review':False,'complete_dependency_review':False,'primary_review_scope':('Literal problem and adjacent Update in Hayman1809.07200v1; no referenced underlying proof read' if hay else 'Original Egres site timed out; retained successor theorem/selected proof passages read' if succ else 'Record statement only; no primary-body clearance'),'self_subsumption_check':('Adjacent Update and printed examples checked; existing resolution/partial result or scope restriction recorded in reason' if hay else 'Successor statements, examples/class inclusions and partial proofs checked; not a new theorem' if succ else 'Printed record examples and known baselines read; original primary body not reviewed'),'evidence_level':('primary_statement_plus_adjacent_update' if hay else 'record_plus_successor_partial_proof' if succ else 'record_only'),'prior_status':'not_cleared; bounded rejection only','accepted_or_history_scope':'r304 bound administrative index; no new credit; no status inferred from empty solutions'})
put('dispositions.json',rows);put('proposals.json',[]);put('record-refs.json',refs)
accepted=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text())
history=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text())
# Every accepted family scope is retained in administrative original and read here; no copied history tree.
put('exclusion-check.json',{'accepted_family_count':accepted['accepted_family_count'],'reviewed_family_numbers':[f['number'] for f in accepted['families']],'exact_id_associations':[{'mathdb_id':n,'family':f['number'],'scope':f['scope']} for f in accepted['families'] for a in f.get('record_associations',[]) for n in [a['mathdb_id']] if str(n) in notes],'history_top_keys':list(history),'cayley364119':'excluded by r363; not reserved; source already contains equal-max unequal-avoidance example','coverage_baseline':683,'root_reconciliation_required':True})
put('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scientific_input_freeze':'bindings.json before record parsing','sources':'sources.json; raw content sha256 written before text extraction','immutable_refs':'flat original paths; no corpus or recursive history copies','source_reading':['Hayman Problems2.66,3.23,4.23,5.18,6.75,6.104,7.35,7.52,7.62,8.6 and adjacent Updates','Orientation successor2603.09475v1 pp2-3 statements; Lemma3.2 and Sections3.1-3.3 selected proofs','Matroid successor1911.09890v1 Theorems1-2; Algorithm2 and selected proof sections pp8-10'],'mathdb_requests':0,'computation':'No mathematical sweeps; input verification, extraction, packaging only','counts':{'additional':9,'total':39,'next':40},'novelty':'No new result claimed; no live proof-registry clearance claimed or needed for rejected leads'})
# Preserve only capped extraction evidence, not another whole corpus or history.
evidence=[]
for name,terms in [('hayman',['Problem 2.66','Update 2.66','Problem 3.23','Update 3.23','Problem 5.18','Update 8.6']),('orientation-successor',['Theorem 1.2','Theorem 1.3','Theorem 1.4','Lemma 3.2.']),('matroid-successor',['Theorem 1.','Theorem 2.','Proof of Theorem 1.','Proof of Theorem 2.'])]:
 lines=(R/'sources'/f'{name}.txt').read_text().split('\n')
 for term in terms:
  for j,s in enumerate(lines):
   if s.startswith(term):evidence.append({'source':f'sources/{name}.txt','start_line':j+1,'text':'\n'.join(lines[j:j+24])});break
put('capped-evidence.json',evidence)
print('built',len(rows),'record dispositions; primary10 successor2 complete0')
