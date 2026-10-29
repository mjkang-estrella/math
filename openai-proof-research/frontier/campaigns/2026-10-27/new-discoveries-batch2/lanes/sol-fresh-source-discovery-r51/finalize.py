import pathlib,json,hashlib,datetime,re
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent;utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prev=json.loads((P.parent/'sol-fresh-source-discovery-r49/registry-screen.json').read_text())
out={'utc':utc,'baseline':'r49','coverage':'named complete cached scopes only; no whole-dev absence or semantic-completeness claim','registries':{}}
for key,old in prev['registries'].items():
 live=json.loads((P/'sources'/f'{key}-head.json').read_text());assert live['sha']==old['head']
 scopes=[]
 for sc in old['scopes']:
  path=pathlib.Path(sc['reused_from']);assert sha(path)==sc['sha256'];d=json.loads(path.read_text());assert not d.get('truncated',True)
  hits=[x['path'] for x in d['tree'] if any(s in x['path'].lower() for s in ['mathieu','bansal','sokol','krasniqi','nielsen'])]
  scopes.append({'path':str(path),'sha256':sha(path),'entries':len(d['tree']),'truncated':False,'lexical_hits':hits,'original_provenance':sc['original_http_provenance']})
 out['registries'][key]={'head':live['sha'],'head_commit_utc':live['commit']['committer']['date'],'unchanged_from_r49':True,'scopes':scopes}
(P/'registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
context=[]
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B.parents[3]/'AGENTS.md']:
 if p.exists():context.append({'path':str(p),'sha256':sha(p)})
for p in sorted(P.parent.glob('sol-*/SUMMARY.md')):
 if p.parent==P:continue
 # Exclusion reconnaissance; metadata is not a claim to have read full prior-lane mathematical bodies.
 if 'fresh' in p.parent.name or 'discovery' in p.parent.name:context.append({'path':str(p),'sha256':sha(p),'read_scope':'summary reconnaissance; full source mathematical reading not inherited'})
(P/'context-screen.json').write_text(json.dumps({'utc':utc,'files':context,'relevant_full_predecessor_reads':['r49 SUMMARY/discovery/registry/fetch/caps/refresh','r47 named-scope tree paths; reuse hashes verified'],'exclusions':'user-supplied and NEXT r1..49 families excluded; no materially new mechanism asserted for any exhausted family'},indent=2)+'\n')
http=[json.loads(s) for s in (P/'http.jsonl').read_text().splitlines()]
prov={'utc':utc,'lane':str(P),'status':'NO ELIGIBLE NOMINATION','credit':0,'root_acceptance_untouched':True,'counts_observed':{'additional':6,'total':36},'primary_source':{'url':'https://files.ele-math.com/articles/jmi-13-64.pdf','sha256':sha(P/'sources/mathieu.pdf'),'statement':'final unnumbered conjecture p917','literal_scope':'all complex r with Re r>0; h_r convex univalent and normalized Mathieu series starlike','actual_result_scope':'all positive REAL r convexity ordinary argument; complex clause routine coefficient exclusion','complete_substantive_literal_resolution':False},'http_sourcebytes':http,'access_limits':{'http_failures':[],'all_actual_fetch_statuses':[x.get('status') for x in http],'no_bypass':True,'search_limits':'bounded public exact-title/conjecture/multiplier searches; no exhaustive citation, MathSciNet/zbMATH, worldwide or full-dev audit'},'resource_limits':{'AS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'BLAS_threads':1,'group':'40ms sampled RSS and CPU; transients and reaped-child CPU not exhaustively measured'},'dependencies':['elementary Fourier and Poisson identities','analytic minimum principle','Schwarz lemma','classical convexity criterion as explicitly stated in actual 2023 primary body'],'strongest_objection':'substantive real theorem is restricted relative to literal complex quantifier; full complex refutation is routine/domain ineligible','remaining_gaps':['No source-scope eligibility adjudication','No independent ordinary-math review','No exhaustive classical multiplier subsumption screen','No full substantive literal source theorem nominated'],'checks':'run.sh; checks.json diagnostics only; no finite completion claim','files':{str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name!='provenance.json'},'external_actions':{'browser':False,'publishing':False,'uploads':False,'accounts':False,'messages':False,'git':False,'children':False,'other_lane_writes':False}}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps({'status':'written','utc':utc,'sources':len(http),'scope_checks':sum(len(x['scopes']) for x in out['registries'].values())}))
