import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(15,15));signal.alarm(20)
from pathlib import Path
import json,hashlib,datetime,shutil
b=Path(__file__).resolve().parent;r=b.parents[5];campaign=b.parents[1]
# Resolve repository directly from campaign hierarchy, without git.
while not (r/'sources/upstream.json').exists():r=r.parent
old=b.parent/'sol-fresh-source-discovery-r31/sources'
def rec(p):
 data=p.read_bytes();return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
inputs={}
for p in [r/'AGENTS.md',campaign/'AGENTS.md',campaign/'ledger.json',campaign/'NEXT.md',campaign/'prior-campaign-context.json',r/'sources/upstream.json',r/'sources/CONTENTS.md',b.parent/'root-symmetric-hankel-preliminary-r1/EXCLUSION.json']+list(campaign.glob('lanes/sol-fresh-*/SUMMARY.md')):
 if p.is_file() and p.parent!=b:inputs[str(p.relative_to(r))]=rec(p)
terms=['brownianenergy','brownian-energy','inclusion','caputo','kim-sau','kim_sau','kmp','radon','youden','unlink']
inventories={}
for n in ['omega-D5.json','omega-Problems.json','omega-main-full.json','inherited-aim-full-current-tree.json','inherited-count-count-full-tree.json','inherited-openai-openai-preprints-tree.json']:
 dest=b/'sources'/('cached-'+n);shutil.copyfile(old/n,dest);x=json.loads(dest.read_text());assert not x.get('truncated',False)
 inventories[n]={'input':str((old/n).relative_to(r)),'cached_at_r31':True,'file':str(dest.relative_to(b)),**rec(dest),'entries':len(x['tree']),'truncated':x.get('truncated',False),'term_hits':[v['path'] for v in x['tree'] if any(t in v['path'].lower() for t in terms)]}
heads={n:json.loads((b/'sources'/f'{n}-head.json').read_text())['sha'] for n in ['openai','count','omega','omega-main','aim']}
delta=json.loads((b/'sources/omega-delta.json').read_text());assert delta['status']=='ahead' and delta['total_commits']==4 and len(delta['files'])==5
screen={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':heads,'inventories':inventories,'omega_delta':{'base':'f9745e6af0bfa02fc8c61013f48003ce3e4f9606','head':heads['omega'],'total_commits':4,'files':[{'path':p['filename'],'status':p['status']} for p in delta['files']]},'coverage':'Complete inherited scoped paths plus small Omega delta; not complete whole-dev or semantic/full-body prior-art coverage. No exact prior proof located; no novelty PASS.'}
(b/'registry-screen.json').write_text(json.dumps(screen,indent=2))
searches=['site.clopen.net conjecture probability inequality','site.github.com MColbrook conjecture AIM mathematics','"Gaussian" "intersection" "log-concavity" "Chan" Radon','"Brownian energy" "spectral gap" conjecture degree two','"Unimodality for Radon partitions" proof conjecture 7.2','"Brownian energy" "degree" "two" spectral gap proof conjecture 2026','"One- and two-particle spectral gap identities" Kim Sau 2026','"Aldous spectral gap phenomena" "Brownian"','Federico Sau webpage publications symmetric inclusion spectral gap','"Brownian energy" "counterexample" "two"','"two-particle spectral gap" "proof" "2026" -site:emergentmind.com -site:clopen.solutions','"Brownian energy" site:github.com/openai/math']
(b/'search-log.json').write_text(json.dumps({'utc_date':'2026-10-29','queries':searches,'method':'public web search; primary bodies separately fetched in http.json','limit':'Search snippets/listings do not certify absence of a proof.'},indent=2))
assert not (b/'PROOF.md').exists();assert not list(b.rglob('*.lean'))
for n in ['checks.json','probe-results.json','targeted-results.json']:json.loads((b/n).read_text())
artifacts={str(p.relative_to(b)):rec(p) for p in sorted(b.rglob('*')) if p.is_file() and p.name!='provenance.json'}
p={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'Full Brownian-energy degree-two source question remains unresolved here; no nomination','credit':0,'additional_accepted':5,'total_accepted':35,'root_owns_acceptance':True,'write_scope':str(b),'source_target':{'author':'Kim–Sau; Caputo–Quattropani–Sau','published_doi':'10.1007/s00220-026-05728-9','published_date':'2026-09-27','published_label':'Section1.3 Eq1.7','latest_preprint':'https://arxiv.org/html/2412.01489v2','preprint_label':'Section1.3 Eq1.10','followup':'https://arxiv.org/html/2609.10450v1','followup_date':'2026-09-09','followup_label':'Section1.4.6 Eqs1.98–1.99'},'heads':heads,'resource_limits':{'AS_bytes':536870912,'checks_CPU_seconds':25,'probe_CPU_seconds':35,'targeted_CPU_seconds':40,'wall_outer_seconds_max':55,'BLAS_threads':1,'max_enumerated_states':1000,'max_actual_states':816},'strongest_objection':'No uniform all-degree inequality or exact degree>=3 counterexample. Existing calculations are classical consistency checks and known degree-one failures.','access_limits':['Wrong guessed versions404; corrected from live records','Wrong author URL login redirect; no login','Caputo author TLS certificate failure; no bypass/retry','Full current whole-dev coverage unavailable; complete scoped inventories plus delta only','Bounded semantic/author/citing-body screen, no specialist exhaustive review or priority guarantee'],'formal':{'run':False,'candidate':False,'reason':'No full ordinary theorem/refutation; no PROOF.md or Lean investment warranted'},'inherited_inputs':inputs,'artifacts':artifacts}
(b/'provenance.json').write_text(json.dumps(p,indent=2));print(json.dumps({'status':'audit PASS','files':len(artifacts),'inputs_hashed':len(inputs),'heads':heads,'credit':0}))
