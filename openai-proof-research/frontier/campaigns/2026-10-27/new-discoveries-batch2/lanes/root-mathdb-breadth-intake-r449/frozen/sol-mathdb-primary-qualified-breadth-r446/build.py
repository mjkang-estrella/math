import json,pathlib,hashlib,collections
R=pathlib.Path(__file__).resolve().parent;L=R.parent
def put(n,j):(R/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def h(b):return hashlib.sha256(b).hexdigest()
records=json.loads((R/'assigned-records.json').read_text());assess={}
for line in (R/'assessment.tsv').read_text().splitlines():
 i,status,scope,reason=line.split('\t');assess[int(i)]=(status,scope,reason)
assert len(assess)==50
levels={401928:('owr2018-50', [28,29],'determinant.txt:951-980,1080-1150,1214-1230; exact statements, matrix algorithm and terminal proof read; subordinate lemmas not fully replayed'),401932:('owr2018-50',[34,35],'report theorem and contemporaneous resolution note; no proof of sharpened bound read'),401935:('owr2018-50',[39],'problem definition and approximation discussion only'),401940:('owr2018-50',[46],'literal problem only; no reduction executed'),402069:('owr2019-13',[55,56],'boolean.txt:30-80 definitions and Theorem1 read; complete semiprobabilistic proof not read'),402118:('owr2019-19',[20],'literal source sentence only'),402119:('owr2019-19',[20],'RIP definitions and hardness discussion only'),402128:('owr2019-19',[43],'localization mechanism introduction only'),402135:('owr2019-19',[61,62],'treecover v4 theorem locations; treecover-successor v3 Section4 lower-bound example and translation citation read; dependency closure not read'),402140:('owr2019-19',[68],'source extremal bounds and open question'),402196:('owr2019-27',[43],'multiscale v3 Theorems1.2-1.3 read; long construction proof not read'),402310:('owr2019-39',[25,26,27],'sumcomplex v1 definitions, internal RP2 and n7 example and theorem discussion; proof not fully read'),402406:('owr2019-47',[24,25],'heisenberg v2 Sections4.1-4.2.2, Lemma4.1, Proposition4.3 and full Theorem1.7 proof read; global functional-analysis/Fourier dependency closure not replayed')}
# Record explicit original historical matches without displaying unrelated scientific records.
def matches(obj,ids):
 found=set()
 if isinstance(obj,dict):
  for k,v in obj.items():
   if k.isdigit() and int(k) in ids:found.add(int(k))
   if k in ('mathdb_id','related_mathdb_id') and isinstance(v,int) and v in ids:found.add(v)
   found|=matches(v,ids)
 elif isinstance(obj,list):
  for v in obj:found|=matches(v,ids)
 return found
ids=set(assess); hist={n:sorted(matches(json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text()),ids)) for n in ['accepted-exclusions.json','historical-dispositions.json']};assert not any(hist.values()),hist
put('history-reconciliation.json',{'assigned_matches':hist,'r363_excluded':364119,'excluded_ids':[372627,372628,368940,404067,364119],'baseline_reported_distinct_reviews':2533,'queue_metadata_counted_as_review':False,'counts':{'additional':9,'total':39,'next':40}})
D=[]
for x in records:
 j=x['record'];i=j['mathdb_id'];status,scope,reason=assess[i];lev=levels.get(i)
 D.append({'mathdb_id':i,'canonical_url':j['canonical_url'],'title':j['title'],'literal_statement':j['statement'],'literal_statement_sha256':x['literal_sha256'],'canonical_record_sha256':x['canonical_sha256'],'canonical_statement_sha256':h(json.dumps(j['statement'],sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'canonical_encoding':'UTF-8 JSON sort_keys=True ensure_ascii=False separators=(comma,colon); canonical_record hashes entire normalized record; canonical_statement hashes JSON string','original_record':{'path':x['original'],'line':x['line']},'scope_quantifiers':scope,'disposition':status,'reason_and_general_mechanism':reason,'primary_source':{'url':j['source_url'],'level':'body_sections_read' if lev else 'literal_normalized_record_only','local_text':'sources/'+lev[0]+'.txt' if lev else None,'pdf_pages_read':lev[1] if lev else [],'not_inferred_from_tags':True},'proof_level':lev[2] if lev else 'No primary proof read; no source clearance claimed.','registry_level':{'status':'HOLD','reason':'No current MathDB/live proof-registry clearance; zero MathDB requests by instruction; inherited 403 routes not revisited. Cached empty solution arrays provide no clearance.'},'decisive_bounded_check':{'executed':'Literal full-statement and quantifier analysis; original/canonical integrity and disjointness checks. '+('Primary sections compared as listed.' if lev else 'No primary theorem or computational certificate checked.'),'planned':'Only reopen with exact primary/successor scope and current registry available; resolve the specific obstacle in reason_and_general_mechanism before any proof investment.','expensive_sweep_executed':False},'certificate_size':'No new certificate. '+('Public theorem/source evidence retained; not a discovery certificate.' if status.startswith('RETIRE') else 'No bounded full-scope certificate size justified; finite instances would not settle this scope.'),'formal_dependencies':'No Lean work. Any future endpoint must formalize the exact source objects and universal hypotheses in scope_quantifiers, with all bridges and dependency closure checked.','strongest_objection':reason,'prior_gap':'Current registry unavailable; primary/successor closure limited exactly as above. No novelty, hardness or global-public-status claim.','brief_proposed':False,'discovery_credit':0})
put('dispositions.json',D);put('proposals.json',[])
put('source-review.json',{'levels':{str(i):{'text':v[0],'pages':v[1],'reading':v[2]} for i,v in levels.items()},'downloads_are_not_full_reading':True,'dependency_closure_replayed':False,'versions':{'heisenberg':'1902.05475v2 27Nov2019','determinant':'1805.11245v4 (header retained in source text)','scaling':'downloaded, no theorem/proof clearance based on it','multiscale':'1910.13492v3 27Nov2024','sumcomplex':'0903.1359v1; PDF title date Nov1 2018, retained without chronology repair','treecover':'1902.05055v4 4Aug2020','treecover-successor':'2109.02569v3 5Jul2022','boolean':'1711.08215v1 22Nov2017'}})
# Add excerpts for all read report pages, plus exact proof passages supporting strongest retirements.
ex=json.loads((R/'source-excerpts.json').read_text());seen={(e['file'],e['pdf_page']) for e in ex}
for n,pages,_ in levels.values():
 txt=(R/'sources'/f'{n}.txt').read_text().split('\f')
 for p in pages:
  if (f'sources/{n}.txt',p) not in seen:ex.append({'file':f'sources/{n}.txt','pdf_page':p,'text':txt[p-1]});seen.add((f'sources/{n}.txt',p))
put('source-excerpts.json',ex)
print(dict(collections.Counter(x['disposition'] for x in D)))
