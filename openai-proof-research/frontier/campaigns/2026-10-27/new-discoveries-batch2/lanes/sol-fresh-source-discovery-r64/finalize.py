import json,hashlib,datetime,re
from pathlib import Path
from html.parser import HTMLParser
P=Path(__file__).resolve().parent;batch=P.parent.parent;repo=batch.parents[3]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','h2','h3','h4','h5','h6','div']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
for name in ['metallic','metallic-older','christoffel','koizumi-243']:
 p=P/'sources'/(name+'.html')
 if p.exists():
  x=Text();x.feed(p.read_text());(P/'sources'/(name+'.txt')).write_text(''.join(x.parts))
contexts=[repo/'AGENTS.md',batch/'AGENTS.md',batch/'ledger.json',batch/'prior-campaign-context.json',batch/'NEXT.md',batch/'lanes/root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json']+[batch/('lanes/sol-fresh-source-discovery-r'+str(n)+'/SUMMARY.md') for n in [60,61,63]]
rows=[]
for p in contexts:
 if p.exists():rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
regs=[]
for name in ['omega-D5.json','omega-Problems.json']:
 p=batch/'lanes/sol-fresh-source-discovery-r57/sources'/name
 x=json.loads(p.read_text());matches=[r['path'] for r in x['tree'] if re.search('koizumi|pseudogreedy|ahmes|metallichankel|metallic-hankel',r['path'],re.I)]
 regs.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree_sha':x['sha'],'truncated':x.get('truncated'),'matches':matches,'coverage':'Blueprint/D5 markdown only, NOT Lean tree' if 'D5' in name else 'Problems markdown'})
http=[json.loads(l) for l in (P/'http.jsonl').read_text().splitlines()]
prov={'lane':P.name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'status':'full source Conjecture C unresolved; no nomination','root_counts_unchanged':{'additional':7,'total':37},'primary_selected':{'authors':['Guo-Niu Han','Emmanuel Pedon'],'url':'https://arxiv.org/html/2610.36132v1','version':'v1, submitted 2026-10-26; live abstract lists only v1','statement':'Conjecture C in Section 1, every n>=1, ell>=n+3, all residues and all m>=0; period rho parity-dependent','published_version':'No journal version claimed'},'source_requests':http,'source_hashes':[{ 'path':str(p.relative_to(P)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted((P/'sources').iterdir()) if p.is_file()],'context':rows,'registry_snapshot_screen':regs,'registry_freshness':{'status':'HOLD','inherited_block':'shared API HTTP403','api_calls_this_lane':0,'reset':'No usable reset information in inspected inherited provenance; no API retry','latest_observed_head':'6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3','observed_time_inherited':'2026-10-29 15:49 UTC','is_current_head':False,'raw_content_reads':'Exact known immutable paths only; not head refresh or actual Lean-tree delta clearance'},'actual_public_lean_bodies':['sources/omega-transfer.lean','sources/omega-cofactor.lean','sources/omega-data.lean','sources/omega-golden.lean'],'public_lean_compiled':False,'access_gaps':['No current registry HEAD refresh or complete actual Lean-tree delta audit','No exhaustive MathDB/specialist registry clearance','No independent proof review; full ordinary proof absent','Older published Christoffel formula does not by itself provide all normal-gap and initial-index bridges'],'resource_limits':{'AS_bytes':512*1024**2,'sampled_group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'sample_interval_seconds':.04,'BLAS_threads':1,'unsampled_transients_excluded':False},'external_mutations':False,'search_queries':['site.math.colgate.edu/~integers/ 2026 Conjecture polynomial','Koizumi pseudo-greedy conjecture proof','metallic Hankel quasi-polynomial','Hankel Christoffel vanishing determinants'],'novelty_limits':'No priority or full classical-subsumption clearance; public unboundedness excluded; public all-n first-order transfer is a significant routine-bridge objection.'}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
(P/'context-registry-screen.json').write_text(json.dumps({'contexts':rows,'registry':regs},indent=2)+'\n')
print('provenance sources',len(http),'context files',len(rows),'registry matches',sum(len(r['matches']) for r in regs))
