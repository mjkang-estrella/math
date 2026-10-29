import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger=json.loads((B/'ledger.json').read_text()); prior=json.loads((B/'prior-campaign-context.json').read_text())
context={'utc':now,'counts':[ledger['accepted_count'],ledger['total_accepted_count']],'accepted_current':[x['title'] for x in ledger['accepted']],'prior_inventory':prior,'context_files':[],'excluded_new_family':'real Mathieu real convexity/starlikeness: exact LMZ1976 p115 complex Bernardi bridge; do not revisit'}
files=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'lanes/root-real-mathieu-exclusion-r1/EXCLUSION.json']
files += [B/('lanes/sol-fresh-source-discovery-r'+str(n)+'/SUMMARY.md') for n in [44,45,46,47,49,51]]
files += [B/'lanes/sol-plucking-full-discovery-r2/SUMMARY.md']
for p in files:context['context_files'].append({'path':str(p),'sha256':sha(p)})
(P/'context-screen.json').write_text(json.dumps(context,indent=2)+'\n')
old=json.loads((B/'lanes/sol-fresh-source-discovery-r51/registry-screen.json').read_text())
r={'utc':now,'baseline':'user b386687d1b21d80059f9b18b696db3503dbfa340; earlier named scopes from r47/r51','coverage':'named complete cached scopes plus lawful live deltas only; no whole-dev absence guarantee','registries':{},'body_comparisons':{'0-1':'actual new compact minimal real-flow mixing theorem; no median inequality','2-3':'Karp incomplete-beta coefficient Turanian positivity, not quantile bounds','4-5':'Karp first-parameter coefficient signs, not quantile bounds'}}
for k,v in old['registries'].items():
 d=json.loads((P/'sources'/(k+'-head.json')).read_text()); scopes=[]
 for s in v['scopes']:
  p=pathlib.Path(s['path']);tree=json.loads(p.read_text());assert sha(p)==s['sha256'];assert not tree['truncated']
  scopes.append({'path':str(p),'sha256':sha(p),'entries':len(tree['tree']),'truncated':False,'lexical_hits':[x['path'] for x in tree['tree'] if any(q in x['path'].lower() for q in ['median','beta','kerman','lyon'])]})
 r['registries'][k]={'head':d['sha'],'commit_utc':d['commit']['committer']['date'],'scopes':scopes}
delta=json.loads((P/'sources/omega-delta.json').read_text())
r['omega_delta']={'total_commits':delta['total_commits'],'returned_commits':len(delta['commits']),'files':[x['filename'] for x in delta['files']],'chronology':[{'sha':c['sha'],'utc':c['commit']['committer']['date'],'message':c['commit']['message']} for c in delta['commits']]}
(P/'registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
prov={'utc':now,'lane':str(P),'credit':0,'campaign_counts_observed':[6,36],'root_alone_accepts':True,'primary_candidates_screened':2,'selected':'Kerman1111.0433v1 all a,b>1 relative error<4%','http':[json.loads(x) for x in (P/'http.jsonl').read_text().splitlines()],'source_versions':{'kerman':'1111.0433v1 only;2011-11-02','lyon':'2610.33859v1 only;2026-10-24T19:05:32Z','memoir':'1412.1481v4;2016-05-07T22:07:41Z','convex':'2005.08204v4;2020-12-31T11:51:53Z'},'access_gaps':['MDPI2024 theorem bodies403;stopped','Lyon longer beta-bound manuscript mentioned in Section8 unread','journal memoir revision not compared separately'],'novelty_status':'NOT CLEARED; no located full bridge in read bodies does not establish absence','mathematical_status':'INCOMPLETE; exact covariance/kernel gaps in discovery.md','resource_caps':{'AS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'BLAS_threads':1,'process_group_RSS_CPU_sampling':True},'external_mutations':False,'children':False,'git_operations':False,'artifact_hashes':{}}
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name!='provenance.json':prov['artifact_hashes'][str(p.relative_to(P))]=sha(p)
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps({'artifacts':len(prov['artifact_hashes']),'credit':0,'utc':now,'heads':{k:v['head'] for k,v in r['registries'].items()}}))
