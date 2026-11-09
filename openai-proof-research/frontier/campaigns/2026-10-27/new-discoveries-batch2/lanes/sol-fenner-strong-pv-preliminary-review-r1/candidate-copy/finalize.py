from pathlib import Path
import json,hashlib,datetime,re
b=Path(__file__).resolve().parent
D=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=b.parent/'sol-mean-cascade-current-prior-audit-r1'/'sources'
reused=[]
for n,count in [('openai-preprints-tree.json',13578),('count-full-tree.json',183)]:
 p=base/n;j=json.loads(p.read_text());assert j['truncated'] is False and len(j['tree'])==count
 reused.append({'path':str(p),'sha256':D(p),'entries':len(j['tree']),'truncated':j['truncated']})
patterns={'final_target':'fenner|extrapolat|strong.?pv|quasicrystal|convexity.region','excluded_arimoto':'arimoto|hirche|renyi.combin|gerber'}
screens=[]
for p in [b/'sources'/'omega-D5-tree.json',b/'sources'/'omega-Problems-tree.json',base/'openai-preprints-tree.json',base/'count-full-tree.json']:
 j=json.loads(p.read_text());assert j['truncated'] is False
 screens.append({'file':str(p),'sha256':D(p),'entries':len(j['tree']),'matches':{k:[e['path'] for e in j['tree'] if re.search(v,e['path'],re.I)] for k,v in patterns.items()}})
(b/'final-registry-screen.json').write_text(json.dumps(screens,indent=2))
queries=[
 'site:mathdb.com "conjecture" "convexity" -Le -Roy -arcsinh -Gamma',
 'site:arxiv.org "conjecture" "log-convexity" 2026',
 'Hirche Arimoto information combining conjecture 2026 convexity concavity 2004.14408',
 'Fenner Green Homer convexity region unbounded transcendental conjecture resolved',
 '"Arimoto" "convexity" "Hirche" conjecture',
 '"Conjecture IV.6" "Rényi"',
 '"Mrs. Gerber" "Arimoto" convexity 2026',
 '"Fenner" "strong PV" conjecture discrete',
 '"Fixed-Parameter Extrapolation" "conjecture" proof',
 '"Pinch" "lambda-convex" discrete algebraic',
 '"strong PV" "integer polynomials" proof conjecture',
 '"Fenner" "Conjecture 11.1" discrete',
 '"lambda-convex" "converse" "integer"',
 '"integer polynomials" "prescribed" "conjugates" approximation']
(b/'search-log.json').write_text(json.dumps({'date_utc':'2026-10-29','engine':'web.run','queries':queries,'coverage':'bounded public search; actual primary/companion bodies fetched separately; search result snippets not proof evidence','onpoint_urls':['https://link.springer.com/article/10.1007/s00454-025-00816-4','https://arxiv.org/abs/1212.2889','https://mathcs.clarku.edu/~fgreen/papers/sigactopen.pdf']},indent=2))
inputs=[]
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 root=b.parents[5];p=root/rel
 if p.exists():inputs.append({'path':str(p),'sha256':D(p)})
hist=json.loads((b/'sources'/'arimoto-history.json').read_text())
p={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ordinary full proof candidate; independent review and eligibility unresolved','source_claim':{'doi':'10.1007/s00454-025-00816-4','label':'Conjecture11.1','published_utc':'2026-06-11','scope':'all complex lambda, full iff strong PV discreteness','actual_published_body':'sources/fenner.html','closest_companion':'sources/fenner-open.pdf','external_known_dependency':'arXiv1212.2889v6 Theorem8.2 (discrete implies algebraic integer)'},'http':json.loads((b/'http.json').read_text()),'registry':json.loads((b/'registry.json').read_text()),'reused_verified_complete_trees':reused,'public_arimoto_history':[{'sha':x['sha'],'utc':x['commit']['committer']['date']} for x in hist],'input_hashes':inputs,'all_lane_sources':{str(x.relative_to(b)):D(x) for x in (b/'sources').iterdir() if x.is_file()},'checks':'checks.json; exact bounded identity diagnostics, not universal verification','novelty_limits':['no worldwide absence claim','registry path search not whole-registry fulltext','Pinch/Meyer and integer approximation literature not exhaustively body-read','possible classical subsumption and routine-corollary objection unresolved'],'formal_status':'no Lean code, no compilation claim','credit_assigned':False,'external_mutations':False}
(b/'provenance.json').write_text(json.dumps(p,indent=2))
print(json.dumps({'sources':len(p['all_lane_sources']),'reused_trees':reused,'input_hashes':len(inputs),'created_utc':p['created_utc']},indent=2))
