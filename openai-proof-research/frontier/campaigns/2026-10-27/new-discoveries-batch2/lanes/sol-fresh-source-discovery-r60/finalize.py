from pathlib import Path
import json,datetime,hashlib
P=Path(__file__).resolve().parent;batch=P.parent.parent
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
context=[]
for p in [batch/'ledger.json',batch/'prior-campaign-context.json',P.parent/'root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json']:
 d=json.loads(p.read_text());context.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'top_keys':list(d),'accepted_titles':[a.get('title') for a in d.get('accepted',[])]})
(P/'context-screen.json').write_text(json.dumps(context,indent=2))
counts={}
for stem in ['checks','deep','deep-incomplete']:
 d=json.loads((P/(stem+'.json')).read_text());rows=d['cases'];counts[stem]={'completed':len(rows),'all_pass':all(r['pass_interval'] for r in rows),'max_dimension':max(r['dimension'] for r in rows)}
for stem in ['moments','moments-incomplete']:
 rows=json.loads((P/(stem+'.json')).read_text());counts[stem]={'completed':len(rows),'all_residues_nonnegative':not any(r['bad'] for r in rows),'max_dimension':max(r['dimension'] for r in rows)}
requests=[json.loads(l) for l in (P/'http.jsonl').read_text().splitlines()]
meta={'lane':P.name,'utc':utc,'credit':0,'status':'full source root-location unresolved; no nomination','root_counts_unchanged':{'additional':7,'total':37},'source_requests':requests,'source_versions':{'chapoton':'2503.04247v2 latest; journal login blocked','preorder':'2605.26916v1 current abstract only version','closest_chain':'2510.23903v3 latest, supersedes initially read v2','closest_octopus':'2603.11654v1 only version','mu':'2503.24076v2 latest, screened then deferred'},'registry':{'freshness':'HOLD','inherited_latest_observed_head':'6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3','inherited_observation_utc':'2026-10-29T15:49:00Z (minute precision)','current_live':'dev README fetched; does not identify exact current head or clear delta','API':'shared403 inherited; no retry/bypass','cached_scope':'r57 Blueprint/D5 markdown and Problems; not actual Lean D5; no cross-format delta claim','closest_bodies':['ChapotonConjectureFiveFourRefutation.md','ChapotonPropositionFiveTwoRefutation.md'],'novelty':'HOLD; no exhaustive prior-art clearance'},'counts':counts,'guards':{},'resource_caps':{'AS_bytes':536870912,'sampled_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'BLAS_threads':1,'sample_period_seconds':0.04},'external_mutations':False,'children':False,'PROOF_md':False}
for p in P.glob('*guard.json'):
 if p.name=='finalize-guard.json':continue
 try:meta['guards'][p.name]=json.loads(p.read_text())
 except:meta['guards'][p.name]={'parse_error':p.read_text()}
meta['access_failures']=['Journal HTTP200 final_url /math/login is not article access','Inherited GitHub API403; no latest complete registry refresh']
meta['hashes']={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest() for p in P.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['provenance.json','finalize.log','finalize-guard.json']}
(P/'provenance.json').write_text(json.dumps(meta,indent=2));print(json.dumps(counts,indent=2));print(json.dumps(meta['guards'],indent=2))
