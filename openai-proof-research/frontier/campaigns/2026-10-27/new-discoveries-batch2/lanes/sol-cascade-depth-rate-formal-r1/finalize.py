import pathlib,json,hashlib,re,resource,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
b=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((b/'frozen-before.json').read_text())
after={p:h(pathlib.Path(p)) for p in before}
assert after==before
(b/'frozen-after.json').write_text(json.dumps(after,indent=2))
for name in ['DepthDefs','DepthArithmetic','DepthAnalysis','Checks']:
 assert (b/f'formal/{name}.lean').read_bytes()==(b/f'replay/{name}.lean').read_bytes()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',(b/f'formal/{name}.lean').read_text())
 r=json.loads((b/f'replay-{name}.json').read_text())
 assert r['exit']==0 and r['sampled_peakRSS']<3*1024**3 and r['wall']<180
log=(b/'replay-Checks.log').read_text()
for xs in re.findall(r'depends on axioms: \[([^]]*)\]',log):
 assert set(xs.split(', '))<={'propext','Classical.choice','Quot.sound'}
assert len(json.loads((b/'declarations.json').read_text()))==19
assert len(re.findall(r"^'CascadeRate\..*?(?:axioms|any axioms)",log,re.M))==27
pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
assert (pk/'.git/HEAD').read_text().strip()=='d13f23b723b8a846827a245b89c10fc7d3f11612'
for p,sha in json.loads((b/'supplied-inputs.json').read_text()).items():assert h(pathlib.Path(p))==sha
files={str(p.relative_to(b)):h(p) for p in b.rglob('*') if p.is_file() and p.name!='provenance.json' and p.suffix not in ['.olean','.ilean','.c']}
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'closed arithmetic/analysis component PASS; not source theorem acceptance','credit':0,'counts':{'additional':3,'total':33},'namespace':'CascadeRate','theorems':19,'definitions':8,'axioms_allowed':['propext','Classical.choice','Quot.sound'],'personal_inspection':'all 27 exported types and axiom reports inspected in development and replay','fresh_replay':'python replay_all.py; only .lean sources and identical runner copied; cached pinned upstream imports allowed; no inherited local oleans','strict_options':['autoImplicit false','warningAsError true'],'lean_sha256':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','mathlib_HEAD_read_directly':'d13f23b723b8a846827a245b89c10fc7d3f11612','dependency_modules':len(json.loads((b/'dependency-hashes.json').read_text())['modules']),'limits':{'lean_wall_seconds':180,'lean_sampled_RSS_bytes':3*1024**3,'exact_AS_MiB':512,'exact_CPU_seconds':25,'BLAS_threads':1},'root_inputs_preserved':True,'scope_gap':'literal tree/word/family/cascade lower bound to be proved by root; abstract f is not SourceClaim; summability not claimed','commands':['python replay_all.py','python exact_check.py','python dependencies.py','python finalize.py'],'files_sha256':files}
(b/'provenance.json').write_text(json.dumps(result,indent=2))
print('Final strict component audit PASS; source theorem and novelty credit unclaimed')
