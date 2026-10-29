import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[pathlib.Path('openai-proof-research/AGENTS.md'),B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[{'path':str(p),'sha256':H(p),'bytes':len(p.read_bytes())} for p in files],'counts_observed':{'additional':6,'total':36},'credit':0,'exclusions':'User entire list honored; Tsallis prior r5 exclusion encountered at lead stage, not counted as fresh screen.'}
# Parse complete JSON inventories rather than relying on truncated terminal display.
for p in files:
 if p.suffix=='.json':json.loads(p.read_text())
(P/'context-screen.json').write_text(json.dumps(r,indent=2)+'\n')
old=json.loads((P.parent/'sol-fresh-source-discovery-r55/registry-screen.json').read_text());r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'coverage':'Fresh complete named Omega D5 and Problems trees. Other registries unchanged from r55, cached named scopes hash-verified. NOT entire dev or worldwide clearance.','registries':{}}
words=['besselratio','unimodality','ellipse','karpvishnyakova','sturm']
for k,v in old['registries'].items():
 d=json.loads((P/'sources'/f'{k}-head.json').read_text());assert d['sha']==v['head'];scopes=[]
 if k=='omega':paths=[P/'sources/omega-D5.json',P/'sources/omega-Problems.json']
 else:paths=[pathlib.Path(x['path']) for x in v['scopes']]
 for p in paths:
  d0=json.loads(p.read_text());scopes.append({'path':str(p),'sha256':H(p),'entries':len(d0['tree']),'truncated':d0.get('truncated'),'lexical_hits':[x['path'] for x in d0['tree'] if any(w in x['path'].lower().replace('-','') for w in words)]})
 r['registries'][k]={'head':d['sha'],'commit_utc':d['commit']['committer']['date'],'unchanged_from_r55':True,'scopes':scopes}
r['actual_closest_bodies']=['sources/registry-bessel.md','sources/registry-result.md'];r['chronology']=[{'sha':x['sha'],'utc':x['commit']['committer']['date'],'message':x['commit']['message']} for x in json.loads((P/'sources/registry-history-dev.json').read_text())];r['limits']='Lexical filenames only direct inspection; not full body audit of all trees. Source clause refuted publicly October25; unimodality outside public refutation. No noveltyPASS.'
(P/'registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'nomination':False,'source_manifest':[json.loads(x) for x in (P/'http.jsonl').read_text().splitlines()],'derived_sources':[{'path':str(p.relative_to(P)),'sha256':H(p)} for p in sorted((P/'sources').glob('*')) if p.suffix in ['.txt','.png']],'source_gaps':['Published body obtained; preprint log-concavity clause absent from published ending. No complete worldwide classical Sturm-ratio literature audit.','d-nb429 not retried; actual publisher PDF obtained through canonical Springer link. Original journal hostname DNS failure; canonical jos.unsoed journal PDF obtained.','Salazarv1 body read only for closest Bessel question scope; companion corpus not exhaustive.'],'resource_limits':'Copied r55 capped_run.py: AS512MiB CPU210s wall230s BLAS1 group RSS512MiB sampled40ms; no caps raised.','external_mutations':False,'solo':True}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
