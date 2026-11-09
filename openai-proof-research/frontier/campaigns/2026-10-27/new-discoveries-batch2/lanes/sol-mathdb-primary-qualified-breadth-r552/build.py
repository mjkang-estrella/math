import pathlib,json,hashlib,collections,re
P=pathlib.Path(__file__).resolve().parent;L=P.parent
def w(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
a=json.loads((P/'assigned-records.json').read_text());ass={int(s.split('\t')[0]):s.rstrip().split('\t')[1:] for s in (P/'assessments.tsv').open()};assert len(ass)==50
out=[]
for x in a:
 d={k:v for k,v in x.items() if k!='record'};d.update(source_url=x['record']['source_url'],canonical_url=x['record']['canonical_url'],title=x['record']['title'],disposition=ass[x['mathdb_id']][0],reason=ass[x['mathdb_id']][1],accepted_credit=0,literal_full_statement_read=True,current_registry_cleared=False,full_dependency_review=False,primary_body_review='none',closest_successor_body_review=False)
 if x['mathdb_id'] in [328935,338643,355557,355559]:d['primary_body_review']='selected passage and definitions; see source-provenance.json'
 out.append(d)
w('dispositions.json',out);w('proposals.json',[])
counts=dict(collections.Counter(d['disposition'] for d in out));w('coverage.json',{'baseline_reported_literal_reviews':4733,'assigned_literal_reviews':50,'local_only_potential_total':4783,'root_reconciled':False,'primary_selected_statement_ids':[328935,338643,355557,355559],'primary_documents':3,'complete_primary_bodies':0,'full_dependency_reviews':0,'proposals':0,'credit':0,'dispositions':counts})
pro=[]
for name,aid,ids,scope in [('commutative','1803.03457v1',[338643],'Section5 counting formula, Lemmas17-19, Corollaries3-4, Conjecture5; full construction and all dependencies not audited'),('fishburn','2208.01484v1',[355557,355559],'Definition of Fishburn permutation; Section10 Conjectures10.3 and10.8; selected Section9 generating-tree proof passage, which covers a different class; no bridge asserted'),('young','1410.0106v3',[328935],'Section2 carry transition construction, Definition3.1 pivot-preserving isomorphism, Section6.1 Conjecture4; abstract theorem descriptions only for1089/complete graphs, not their full proof clearance')]:
 pro.append({'path':name+'.html','version':aid,'ids':ids,'url':'https://arxiv.org/html/'+aid.split('v')[0],'exact_version_url':'https://arxiv.org/html/'+aid,'body_read':scope,'whole_body_read':False,'closest_successor_bodies':'unread; no absence inference','full_dependency_clearance':False})
w('source-provenance.json',{'sources':pro,'downloads':'downloads.json contains exact retrieved bytes, UTC, URL and hashes; derivatives bound in derivative-bindings.json before search','live_search':{'utc_date':'2026-10-31','queries':['Maximal commutative subalgebras Grassmann conjecture1803.03457','Fishburn permutations1324 2143 1423 3124','Young graphs Kendrick conjectures14 3'],'result_limit':'Search results only. JIS primary landing page and Transport of patterns by Burge transpose located; neither body fetched/read. ResearchGate and forbidden routes not opened. No result used as proof clearance.'},'registry':'unavailable HOLD; no current absence-of-hits inference','corpus':'r301 originals checked in place; no MathDB requests'})
# Exact key matching, not substring ID matching.
ctx=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());hits=[];ids=set(ass)
def scan(o):
 if isinstance(o,dict):
  direct=set()
  for k,v in o.items():
   if k in ['mathdb_id','mathdb_related_id'] and isinstance(v,int):direct.add(v)
   if k in ['mathdb_ids','problem_ids'] and isinstance(v,list):direct.update(x for x in v if isinstance(x,int))
  if direct&ids:hits.append(o)
  for v in o.values():scan(v)
 elif isinstance(o,list):
  for v in o:scan(v)
scan(ctx);w('context-check.json',{'exact_historical_id_hits':hits,'accepted_families_read':39,'cayley_decision_read':True,'r551_adjudications_preserved':True,'substring_output_warning':'Earlier exploratory substring hits for28 and40 were unrelated IDs and were discarded.'})
print(counts,'exact historical hits',len(hits))
