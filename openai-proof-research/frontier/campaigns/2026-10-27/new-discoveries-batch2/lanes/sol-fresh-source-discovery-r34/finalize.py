import pathlib,json,hashlib,datetime,re,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
b=pathlib.Path(__file__).resolve().parent;R=b.parents[5];B=b.parents[1]
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def info(p):
 d=p.read_bytes();return {'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()}
heads={n:json.loads((b/'sources'/f'{n}-head.json').read_text())['sha'] for n in ['aim','omega','omega-main','openai','count']}
pattern=r'happy|spanning.?tree|tree.?flip|plane.?tree|costas|radon|reconfiguration|associahed|hereditaryflip'
registry={'utc':now,'heads':heads,'scopes':{},'omega_compare_limit':'33 commits returned; files length300 reaches GitHub compare cap: NOT complete delta. Replaced by current complete D5/Problems subtree inventories. Whole dev tree NOT covered.','chronology':'latest compared commit2026-10-29T11:17:47Z; source2024, followup2026-03-05; no same-scope public resolution found; no novelty PASS','actual_bodies':['sources/omega-flip-metric.lean','sources/omega-flip-median.lean','sources/constrained-published.html','sources/trees.html','sources/journal.pdf','sources/classical.pdf']}
paths=list((B/'lanes/sol-fresh-source-discovery-r32/sources').glob('cached*.json'))
paths+=[b/'sources/omega-D5.json',b/'sources/omega-Problems.json']
for p in paths:
 a=json.loads(p.read_text())
 if not isinstance(a,dict) or 'tree' not in a:continue
 registry['scopes'][str(p.relative_to(R))]={**info(p),'entries':len(a['tree']),'truncated':a.get('truncated'),'path_hits':[x['path'] for x in a['tree'] if re.search(pattern,x['path'],re.I)]}
(b/'registry-screen.json').write_text(json.dumps(registry,indent=2)+'\n')
inputs=[R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md']+[B/x for x in ['AGENTS.md','ledger.json','NEXT.md','prior-campaign-context.json']]
for lane in ['sol-fresh-source-discovery-r32','sol-fresh-source-discovery-r33']:
 inputs += [B/'lanes'/lane/x for x in ['SUMMARY.md','discovery.md','provenance.json','registry-screen.json']]
for lane in ['root-fresh-source-r32-handback','root-fresh-source-r33-handback']:inputs+=list((B/'lanes'/lane).glob('*'))
prov={'utc':now,'target':'Convex plane spanning-tree happy-edge conjecture:2024Conj17 convex restriction/2026Conj1','status':'UNRESOLVED_NO_NOMINATION','credit':0,'counts':{'additional':5,'total':35},'acceptance_owner':'root','heads':heads,'inputs_hashed':{str(p.relative_to(R)):info(p) for p in inputs if p.is_file()},'source_access_hold':'GD2026 published version listed by author; document endpoint, canonical DOI and guessed PDF404.2024primary journal obtained.','source_http_log':'http.json','registry_screen':'registry-screen.json','scope':'Solo; only assignedr34lane writes; no git/browser/account/message/upload; no Lean; no truthaudit','limitations':['No all-n theorem or strict universal refutation','No complete whole-Omega-dev coverage','Search snippets are leads, not source proof bodies','Lightweight source retrieval/parsing/rendering was AS/CPU/wall limited but not continuously RSS-monitored; mathematical checker was process-group RSS-monitored','Classical PDF text extraction empty; exactpp652–654 visually read','No independently reviewed ordinary candidate and no noveltyPASS'],'artifacts':{}}
for p in sorted(b.rglob('*')):
 if p.is_file() and p.name!='provenance.json':prov['artifacts'][str(p.relative_to(b))]=info(p)
(b/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print('metadata written',len(prov['artifacts']),'artifacts')
