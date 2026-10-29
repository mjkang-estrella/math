from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent
out={'lane':str(P),'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','worker_credit':0,'additional_accepted_unchanged':7,'total_accepted_unchanged':37,
 'source':{'authors':'Celano, Elder, Hadaway, Harris, Martin, Priestley, Udell','arxiv':'2507.07243v2','target':'Conjecture 6.5','scope':'Every n>=1; exact maximum individual displacement0..n-1; weak unimodality'},
 'http':json.loads((P/'http.json').read_text()),
 'registry':{'freshness':'HOLD','dated_complete_omega':'70af54071bfd4ac098619a9db8c16bb6f7aced11','dated_complete_omega_paths':350009,'dated_complete_openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','dated_complete_openai_paths':174524,'inventory_observed':'2026-10-29T17:20:00Z','relevant_lean_body_read_at':'75fa71fb84c19580a0ea89b3dc7c8158f7aa7446','public_page_head':'11c6ddfe2cea3073341c23f38a9fab84fd53266e','public_page_observed':'2026-10-29T18:04:56.785298+00:00','complete_new_tree_or_delta':False,'external_lean_recompiled':False},
 'full_scope_gap':'No uniform single-crossing proof for coefficient differences; no source counterexample.',
 'strongest_objection':'Global logconcavity and adjacent-size MLR invariants fail exactly; arbitrary weighted fiber mixtures do not preserve unimodality.',
 'resource_limits':{'address_space_bytes':512*1024**2,'group_rss_bytes':512*1024**2,'cpu_seconds':210,'wall_seconds':230,'sampling_ms':40,'blas_threads':1,'cap_raise':False},
 'external_mutations':False,'git_actions':False,'children':0,'proof_file_created':False,
 'artifacts':{}}
for f in sorted(P.iterdir()):
 if f.is_file() and f.name!='provenance.json':out['artifacts'][f.name]={'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
(P/'provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print('provenance artifacts',len(out['artifacts']))
