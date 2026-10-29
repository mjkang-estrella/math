import pathlib,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;G=L/'sol-renyi-registry-gap-closure-r3'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def h(p):
 s=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):s.update(b)
 return s.hexdigest()
def write(n,j):(O/n).write_text(json.dumps(j,indent=2))
# Retain relevant excerpts only, with exact byte/character provenance.
ex=[]
for name,start,end in [('candela-helfgott','    Proposition 2.1.','    We now turn'),('lev-yuster','Proof of Theorem 2:','We close our note'),('hall-paige','Abstract.','                         2. simultaneously'),('three-subgroup','Theorem A.','The proof of the theorem above'),('cantor-mills','1. Let N','4. Explicit constructions.')]:
 p=O/(name+'.txt');t=p.read_text();a=t.find(start);b=t.find(end,a+len(start))
 if a<0:a=0
 if b<0:b=min(len(t),a+8500)
 b=min(b,a+10000)
 q=O/(name+'-excerpt.txt');q.write_text(t[a:b]);ex.append({'source':name,'full_text_sha256':h(p),'full_text_bytes':p.stat().st_size,'excerpt':q.name,'char_start':a,'char_end':b,'excerpt_sha256':h(q),'scope':'bounded primary-body excerpt; source PDF hashes/request UTC in http.jsonl'})
 p.unlink();(O/(name+'.pdf')).unlink()
write('primary-excerpt-provenance.json',ex)
s=json.loads((O/'registry-screen.json').read_text());bs=s['original_cached_bodies'];missing=[]
for ref,p in s['missing']:
 matches=[x for x in bs if x['ref']==ref and x['path']==p];assert matches;missing.append({'ref':ref,'path':p,'cached_body_sources':[{'source':x['source'],'sha256':x['sha256'],'url':x['url']} for x in matches]})
assert all(x['hash_match'] for x in s['intervals'])
fresh=json.loads((O/'fresh-screen.json').read_text());follow=json.loads((O/'follow-body-reads.json').read_text());assert all(x.get('status')==200 for x in follow)
cov={'utc':now(),'recommendation':'CLEAR_BOUNDED','historical_complete_bridge_found':False,'credit':0,'counts':[8,38],
 'intervals':s['intervals'],'interval_commit_sum':sum(x['commits'] for x in s['intervals']),'file_occurrences':sum(x['files'] for x in s['intervals']),'patch_occurrences':sum(x['patches'] for x in s['intervals']),
 'missing_patch_exact_endpoint_closure':missing,'cached_original_bodies_screened':len(bs),'cached_context_json_bodies':sum('/context/' in x['path'] for x in bs),'cached_body_metadata':'registry-screen.json',
 'later_delta':{'base':'0a10157da355f1825f38212dd4c2869925ae6785','end':'7f200dc4fad796eec490994c705245530200fd78','commits':s['later_delta']['commits'],'files':len(s['later_delta']['files']),'missing_patches':sum(not x['patch'] for x in s['later_delta']['files']),'sha256':s['later_delta']['sha256']},
 'fresh_delta':{'base':'7f200dc4fad796eec490994c705245530200fd78','end':'0d4df45e499f5e2d97471c506c555c18fd44920c','commits':fresh['commits'],'files':len(fresh['files']),'missing_patch_paths':[x['path'] for x in fresh['files'] if not x['patch']],'missing_closure':[x for x in follow if x['path']=='Library/PermutationPatterns/colmenarejo2024lucky.md']},
 'fresh_actual_bodies':len(follow),'baseline_additional_bodies':6,'later_additional_bodies':4,'fresh_missing_body':1,
 'screen_scope':'Target-specific textual and JSON-string screen of actual patches and cached bodies; targeted human statement/context reads, not a claim of full semantic theorem audit of every file.',
 'hit_dispositions':{'factorials':'graph-energy coalition weights, truncated Schenker sums, binomial recurrence, oscillator labeling','gamma_terms':'digamma explicit formula, Robin gamma constant, quantum coherence Gamma, lattice Weil phase, circle-placement gamma label','numeric_labels':'unrelated numbered equations','dissociated_factorial_or_same_object':'none located'},
 'inherited_baseline':{'omega_paths':350197,'openai_paths':174524,'preliminary_path_leads':269,'preliminary_actual_bodies':17,'fresh_complete_baseline_body_audit':False},
 'remaining_concrete_exact_object_gaps':[],'adjacent_access_limit':{'source':'Jevtic DOI10.1137/S0895480194265623','status':403,'body_read':False,'load_bearing_for_exact_object_clearance':False,'reason':'generic vector-codebook lead; stronger concrete distinct-subset concentration mechanism inspected in Candela-Helfgott; exhaustive routineness literature classification is not claimed'}}
write('exactcoverage.json',cov)
before=json.loads((O/'freeze-before.json').read_text());after=[]
for x in before['files']:
 p=pathlib.Path(x['path']);y=dict(x);y['sha256']=h(p);y['unchanged_from_before']=y['sha256']==x['sha256'];assert y['unchanged_from_before'];assert y.get('expected',y['sha256'])==y['sha256'];after.append(y)
write('freeze-after.json',{'utc':now(),'files':after,'all_unchanged':True})
guard=L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';assert h(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
inputs=[]
for p in [G/'intervals.json',G/'bodies.json',G/'context-decoding.json',L/'sol-supertoken-preliminary-review-r1/omega-new-delta.json',L/'sol-supertoken-preliminary-review-r1/http.jsonl',L/'root-factorial-preliminary-adoption-r1/DECISION.md',L/'root-factorial-preliminary-adoption-r1/ADOPTION.json',guard]:inputs.append({'path':str(p),'sha256':h(p),'bytes':p.stat().st_size})
http=[json.loads(l) for l in (O/'http.jsonl').read_text().splitlines()]
write('provenance.json',{'utc':now(),'verdict':'CLEAR_BOUNDED','solo':True,'output_lane':str(O),'inputs':inputs,'network_receipts':http,'primary_body_read_scope':{'candela_helfgott':'Definitions1.1-1.3, Theorem1.4, Prop2.1 complete proof pp91-95','lev_yuster':'Theorems1-3 and complete Theorem2 proof','cantor_mills':'definitions, determining-matrix scope, Lemmas1-2, Theorem1 statement','hall_paige':'intro main statement/scope only','three_subgroup':'intro TheoremA/B and companion citation scope only','jevtic':'abstract lead only; body inaccessible403; stopped'},'inherited_body_reads':['ALM full Theorem4.6 and published question','ALS complement paper','Bober integrality classification','Rosser-Schoenfeld prime bound'],'web_search_queries':['dissociated sets subset sums integer vectors entropy Lindstrom Cantor Mills theorem','"t!/t" "Loukaki"','"On the common transversal probability" citations','Lev Yuster size dissociated bases 2011 pdf','"factorial" "dissociated" products','"Loukaki" "probability" "2025"','"factorial" "subset products" equality','"factorial" "t^t" "distinct"','"transversal probability" "Problem 5.6"','"transversal probability" "Problem 12.6"'],'web_search_time_window':{'after':before['utc'],'before':now(),'note':'Tool does not expose exact request UTC; this is a bounding session window, not invented per-query receipts.'},'author_page':'https://sites.google.com/view/marialoukaki/home/publications','freeze_entries':{'candidate':44,'preliminary_review':32,'descriptors':2,'before_after_pass':True},'guard_sha256':h(guard),'limits':{'AS_and_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'sampling_ms':40,'BLAS_threads':1},'failures':['Initial minified intervals output truncated; not treated as semantic read','PDF extraction font-type warning on Hall-Paige; readable theorem text retained','Jevtic web tool inaccessible; direct HTTP403, no retries/bypass'],'credit':0,'counts':[8,38],'no_worldwide_priority_claim':True})
manifest=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name!='final-manifest.json' and '__pycache__' not in p.parts and p.name!='seal-guard.log':manifest.append({'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':h(p)})
write('final-manifest.json',{'utc':now(),'files':manifest,'excludes':['self','__pycache__','seal-guard.log (written by enclosing guard after seal exits)']})
print(json.dumps({'verdict':'CLEAR_BOUNDED','freeze_all_unchanged':True,'missing_patch_closure':len(missing),'manifest_files':len(manifest)}))
