from pathlib import Path
import json,hashlib,collections,datetime
R=Path(__file__).resolve().parent;L=R.parent;A=L/'root-mathdb-breadth-intake-r427'
def put(n,o):(R/n).write_text(json.dumps(o,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def canon(o):return sha(json.dumps(o,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
rows=json.loads((R/'records.json').read_text());asmt={}
for s in (R/'assessments.tsv').read_text().splitlines():
 i,status,scope,mechanism,obstacle=s.split('\t');asmt[int(i)]=(status,scope,mechanism,obstacle)
assert set(asmt)=={o['mathdb_id'] for o in rows}
ex={o['mathdb_id']:o for o in json.loads((R/'source-excerpts.json').read_text())}
loc={o['mathdb_id']:o for o in json.loads((R/'record-locations.json').read_text())}
succ={395266:('foliations','Theorem1; proof lines909-943, Theorem3 dependency; v2 stamp 3Feb2015, body date30Oct2018'),395267:('ellipsoids','Theorems1.1.2,5.2.3; proof lines3656-3690 and finite-class proof plan; published2012 PDF'),395388:('matroid','2017 METR17-01; Sections6 and11, Theorems6.1,11.1,11.3'),395752:('integer-homology','v1 31Aug2018; Theorem1, Section4 Lemma5 and main proof'),395759:('percolation','v2 2Nov2017; Theorems1.3,1.4, proof lines1011-1080')}
out=[]
for o in rows:
 i=o['mathdb_id'];status,scope,mechanism,obstacle=asmt[i]
 out.append({'mathdb_id':i,'title':o['title'],'literal_statement':o['statement'],'statement_sha256':sha(o['statement'].encode()),'canonical_record_sha256':canon(o),'canonicalization':'sorted keys, ensure_ascii=False, compact JSON UTF8 of complete normalized corpus record','record_location':loc[i], 'disposition':status,'scope':scope,'mechanism_screen':mechanism,'reason_and_obstacle':obstacle,'primary_evidence':ex[i], 'levels':{'statement':'full_literal_read','primary':'cited physical report page inspected; adjacent pages individually recorded in extra-excerpts.json where needed','proof':succ[i][1] if i in succ else 'report statement/outline only; full proof dependencies not inspected','registry':'r304 accepted/history and r363 exclusions verified snapshots; current public registry unavailable: HOLD','dependency_closure':'not closed; no acceptance or novelty claim'},'successor':{'file':'sources/'+succ[i][0]+'.txt','inspection':succ[i][1]} if i in succ else None,'calculation':'published percolation bases d3..8 checked in calculations.json' if i==395759 else 'no discovery calculation executed; mechanism screen only','credit':0})
put('dispositions.json',out);put('proposals.json',[])
# Bounded check of the actual published finite construction, not a new result.
def mask(s):return sum(1<<(int(x)-1) for x in s)
sets={3:set(map(mask,['1','2','3','123']))}
changes={4:(['3'],['134','4','234']),5:(['134'],['135','245','12345']),6:(['135','245'],['346','12356','456','23456']),7:(['346'],['13457','24567','12367','1234567']),8:(['13457','24567'],['34568','1234578','34678','25678','2345678'])}
checks=[]
for d in range(3,9):
 if d>3:
  rem,add=changes[d];sets[d]=(sets[d-1]-set(map(mask,rem)))|set(map(mask,add))
 infected=set(sets[d]);steps=0
 while len(infected)<2**d:
  new={v for v in range(2**d) if v not in infected and sum((v^(1<<k)) in infected for k in range(d))>=3}
  assert new;infected|=new;steps+=1
 assert len(sets[d])==(d*(d+3)+5)//6+1
 checks.append({'dimension':d,'initial_set':sorted(sets[d]),'size':len(sets[d]),'infected':len(infected),'steps':steps})
put('calculations.json',{'status':'PASS','kind':'verification of published finite bases only','source':'sources/percolation.txt Theorem1.4 proof','checks':checks,'not_executed':'No new candidate search, threshold estimation, exceptional-class replay, or formal proof. No planned calculation promoted as executed.'})
# Registry snapshots are routing/exclusion evidence, not proof clearance.
reg=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;t=p.read_text()
 reg.append({'original':str(p),'assigned_id_literal_occurrences':[i for i in asmt if str(i) in t],'sha256':sha(p.read_bytes()),'size':p.stat().st_size})
put('registry-screen.json',{'snapshot_search':reg,'r363_excluded':364119,'current_registry_status':'HOLD; no current registry head fetched. Inherited AIProofWatch403 and barred GitHub API/raw/codeload/diff routes not probed. Old snapshots do not establish live absence.','acceptance_or_novelty_clearance':False})
counts=dict(collections.Counter(o['disposition'] for o in out))
put('provenance.json',{'generated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_original_bindings':'bindings.json','baseline_reported_distinct_reviews':2083,'assignment':50,'coverage_claim':'fifty full literal statements and report sections inspected; reported baseline not re-audited','primary_report_downloads':len(json.loads((R/'source-provenance.json').read_text())),'successor_downloads':5,'current_registry':'HOLD','mathdb_requests':0,'other_active_reservations':50,'dispositions':counts,'counts_unchanged':{'additional':9,'total':39,'next':40},'version_limits':'Published report PDFs inspected at cited pages, not complete report proofs or historical-version comparison. Successor PDF stamps retained. No complete dependency closure; no whole-corpus technical-review claim.','search_leads':'Live public search 2026-10-31 found matroid, percolation, foliations, ellipsoids and integer-homology successors. Triangle theorem lead held after403; Muller atomic lead insufficient for molecular scope. Search snippets not used as theorem proof evidence.'})
print(json.dumps({'rows':len(out),'reports':len(json.loads((R/'source-provenance.json').read_text())),'counts':counts,'calculations':'PASS'},indent=2))
