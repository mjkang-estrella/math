import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(30)
from pathlib import Path
import json,hashlib,datetime,re
b=Path(__file__).resolve().parent;c=b.parents[1];r=c
while not (r/'sources/upstream.json').exists():r=r.parent
old=b.parent/'sol-fresh-source-discovery-r32';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def rec(p):return {'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
heads={n:json.loads((b/f'sources/{n}-head.json').read_text())['sha'] for n in ['aim','omega','omega-main','openai','count']}
assert heads['omega']=='5f94e981243583f47844e82a3f385c15372fb4b7'
x=json.loads((b/'sources/omega-delta.json').read_text());assert x['total_commits']==3 and len(x['files'])==7
inventories={};pattern=r'oswald|zhou|truncation|paving|riesz|volterra|(^|[-/_])sor([-/_]|$)'
for p in (old/'sources').glob('cached-*.json'):
 t=json.loads(p.read_text());assert not t.get('truncated',False)
 inventories[p.name]={'input':str(p.relative_to(r)),**rec(p),'entries':len(t['tree']),'truncated':False,'path_hits':[v['path'] for v in t['tree'] if re.search(pattern,v['path'],re.I)]}
reg={'utc':now,'heads':heads,'inherited_scoped_inventories':inventories,'omega_delta':{'base':'953086aaf8dbba50658ea758d655753a486ce219','head':heads['omega'],'total_commits':3,'last_commit_UTC':x['commits'][-1]['commit']['committer']['date'],'files':[{k:v[k] for k in ['filename','status','sha']} for v in x['files']]},'prior_delta':{'path':str((old/'sources/omega-delta.json').relative_to(r)),**rec(old/'sources/omega-delta.json'),'base':'f9745e6af0bfa02fc8c61013f48003ce3e4f9606','head':'953086aaf8dbba50658ea758d655753a486ce219'},'coverage':'Complete inherited D5/Problems plus two complete small deltas, unchanged complete main/OpenAI-preprints/AIM/Count scoped inventories. NOT complete whole-dev or semantic/body coverage. Path hits are leads, never novelty evidence.'}
(b/'registry-screen.json').write_text(json.dumps(reg,indent=2))
inputs={}
for p in [r/'AGENTS.md',c/'AGENTS.md',c/'ledger.json',c/'NEXT.md',c/'prior-campaign-context.json',r/'sources/upstream.json',r/'sources/CONTENTS.md']+list(c.glob('lanes/sol-fresh*/SUMMARY.md')):
 if p.is_file() and p.parent!=b:inputs[str(p.relative_to(r))]=rec(p)
assert not (b/'PROOF.md').exists() and not list(b.rglob('*.lean')) and not list(b.rglob('*.olean'))
checks=json.loads((b/'checks.json').read_text());assert checks['status']=='PASS'
probes=json.loads((b/'probe-results.json').read_text());assert len(probes['rows'])==88
assert all(v['minimum_found']<v['source_threshold'] for v in probes['rows'])
a={str(p.relative_to(b)):rec(p) for p in sorted(b.rglob('*')) if p.is_file() and p.name not in ['provenance.json','guard-results.json']}
p={'utc':now,'target':'Oswald2023 correction Section1 Eq2 p522: universal correlation-matrix sharp2/pi permutation bound','status':'UNRESOLVED; no full candidate','credit':0,'additional_accepted':5,'total_accepted':35,'acceptance_owner':'root','heads':heads,'inputs_hashed':inputs,'artifacts':a,'sources':'Exact requested/final URLs, retrieval UTC, SHA256 and failures in http.json. Inherited inventory paths/hashes in registry-screen.json. Search queries in search-log.json.','strongest_objection':'No all-dimension ordering theorem or exact matrix for which EVERY ordering violates the source threshold. Large fixed-order norms and finite floating minima cannot fill either gap.','limits':['Bounded public/source/author screen, no specialist database or global novelty certification','Omega whole-dev inherited tree truncated, only scoped current coverage','Wrong guessed Omega repo returned422; wrong guessed clopen category404; both preserved; no403/429/challenge encountered','Initial HTML extraction attempted unavailable bs4, then replaced with standard-library extractor','Early read-only metadata snippets and initial probes had shell/individual caps but no RSS sampler; no large/Lean job ran. Final replay all processes guarded45ms/2800MiB and512MiBAS.'],'formal':{'run':False,'reason':'No full ordinary proof; no helper Lean or inherited candidate oleans','type_axiom_origin_unsafe_audit':'Not applicable: zero candidate Lean declarations; no certificate claimed','required_if_future_candidate':'Lean4.34.1 pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; serial-j1 warningAsError autoImplicitfalse; standard3 only; source-only replay and actual declaration type/axiom/origin/unsafe audit'},'runtime':{'AS_bytes_each':536870912,'max_replay_child_CPU_seconds':45,'max_replay_child_wall_seconds':55,'BLAS_threads':1,'RSS_monitor_period_seconds':.045,'RSS_ceiling_MiB':2800,'no_Lean_investment':True},'actions':{'solo':True,'git_operations':False,'browser_tabs':False,'external_messages_uploads_accounts':False,'write_scope':str(b)}}
(b/'provenance.json').write_text(json.dumps(p,indent=2));print(json.dumps({'audit':'PASS','files':len(a),'inputs_hashed':len(inputs),'credit':0,'source_endpoint':False}))
