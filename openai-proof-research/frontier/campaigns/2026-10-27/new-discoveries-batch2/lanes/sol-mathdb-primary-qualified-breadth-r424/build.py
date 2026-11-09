from pathlib import Path
import json,hashlib,collections
O=Path(__file__).parent;L=O.parent
J=lambda p:json.loads(p.read_text())
H=lambda b:hashlib.sha256(b).hexdigest()
loc={x['mathdb_id']:x for x in J(O/'record-locations.json')}; assessments={}
for line in (O/'assessments.tsv').read_text().splitlines():
 i,s,r=line.split('\t'); assessments[int(i)]=(s,r)
records=J(O/'records.json');assert set(assessments)=={r['mathdb_id'] for r in records} and len(assessments)==50
body={393772:('deformations',[(2635,2705)]),393773:('deformations',[(2720,2810)]),393826:('graphs',[(1495,1565)]),393833:('graphs',[(2135,2225)]),393834:('graphs',[(2240,2330)]),393836:('graphs',[(2440,2510)]),393897:('integration',[(2890,2990)]),393898:('integration',[(3445,3490)]),393979:('prop',[(890,990)]),393982:('prop',[]),393989:('prop',[])}
# Only mark actually read ranges. Remaining source access is retained but not body-review evidence.
for i in [393834,393836,393982,393989]:body.pop(i)
excerpts=[]
for i,(name,ranges) in body.items():
 lines=(O/'sources'/f'{name}.txt').read_text().splitlines()
 for a,b in ranges:
  excerpts.append({'mathdb_id':i,'source':f'sources/{name}.txt','first_line':a,'last_line':b,'text':'\n'.join(lines[a-1:b])})
for name,ranges in [('labute-successor',[(1,170)]),('matching-successor',[(1094,1190),(3280,3330)])]:
 lines=(O/'sources'/f'{name}.txt').read_text().splitlines()
 for a,b in ranges:excerpts.append({'source':f'sources/{name}.txt','first_line':a,'last_line':b,'text':'\n'.join(lines[a-1:b])})
(O/'source-excerpts.json').write_text(json.dumps(excerpts,indent=2,ensure_ascii=False)+'\n')
reg=L/'root-mathdb-accepted-exclusions-r304';acc=J(reg/'accepted-exclusions.json');hist=J(reg/'historical-dispositions.json')
assert acc['accepted_family_count']==39
# Lexical ID hits are reported conservatively, not treated as identical mathematical scope.
def hits(o,i):
 return str(i) in json.dumps(o,ensure_ascii=False)
rows=[]
for r in sorted(records,key=lambda x:x['mathdb_id']):
 i=r['mathdb_id'];status,reason=assessments[i];pbody=body.get(i)
 rows.append({'mathdb_id':i,'uuid':r['uuid'],'canonical_url':r['canonical_url'],'title':r['title'],'literal_statement':r['statement'],'statement_sha256':loc[i]['statement_sha256'],'canonical_record_sha256':loc[i]['canonical_sha256'],'record_location':loc[i],'disposition':status,'scope_and_reason':reason,'full_scope_certificate':'No new full-scope certificate established. See reason for candidate mechanism and obstacle.','evidence_levels':{'record':'full literal statement read from hash-verified original normalized corpus; dated snapshot, not live MathDB','primary':'selected problem body and surrounding context read' if pbody else 'source URL recorded; no primary body inspection credited','primary_path':f'sources/{pbody[0]}.pdf' if pbody else None,'proof':('successor sections 5.3 and 13 encoding inspected; earlier structural lemmas and external determinant subroutines not independently audited' if i==393833 else 'primary Hilbert-series equivalence plus successor definitions/Proposition 5 read; external proof dependency not fully audited' if i==393979 else 'no resolution proof body inspected'),'registry':'actual r304 accepted/history and r363 exclusion files hash-verified; no live MathDB registry request','accepted_registry_id_hit':hits(acc,i),'historical_registry_id_hit':hits(hist,i)},'prior_cleared':False,'accepted_credit':0,'brief_qualified':False})
(O/'dispositions.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'proposals.json').write_text('[]\n')
counts=collections.Counter(x['disposition'] for x in rows)
(O/'provenance.json').write_text(json.dumps({'binding_mode':'flat actual original references, no corpus copies and no recursive expansion','bindings':'bindings.json','preflight':'preflight.json','normalization':'canonical record SHA256 over sorted keys, ensure_ascii=False, compact JSON, UTF8; statement SHA256 over literal UTF8','coverage_baseline':1983,'assignment':50,'other_active_reservations':50,'mathdb_requests':0,'retained_primary_bytes':'source-provenance.json','retained_successor_bytes':'independent-successor-provenance.json','denied_successor':'successor-provenance.json','registry_paths':[str(reg/'accepted-exclusions.json'),str(reg/'historical-dispositions.json'),str(L/'root-mathdb-cayley-review-intake-r363/disposition.json')],'counts_unchanged':{'additional':9,'total':39,'next':40},'disposition_counts':dict(counts),'external_search_notes':'Public search used for specific assigned targets. Unsolicited ScienceDirect search results ignored; no ScienceDirect pages opened. Web fetch timeouts on two EMS PDFs preceded successful ordinary direct retrieval; these were not 403/429/challenges. Institutional rigid-body PDF 403 stopped with no retry or alternate route. Inherited AIM/Kourovka/EGRES denials remained parked.','version_coverage':'OWR reports are published 2006 report bodies, not a reconstructed revision history. Matching PDF identifies arXiv v1 2013 and body date 2018; Labute file states 2008 revised 2022. No complete historical-version comparison or broad successor coverage claimed.'},indent=2)+'\n')
print(dict(counts))
