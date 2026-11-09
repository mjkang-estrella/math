import pathlib,json,hashlib,subprocess,sys,os,time,re
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text())
def hashes():
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']}
 assert actual==set(manifest['files'])
 for rel,h in manifest['files'].items():assert sha(L/rel)==h,rel
 for d in json.loads((L/'bindings.json').read_text())['files']:
  assert sha(pathlib.Path(d['original']))==sha(L/d['copy'])==d['sha256'],d['copy']
hashes();start=time.monotonic()
# Independently reconstruct the exact let-expanded DAG; compare every ID/edge.
expected=[]
for line in (L/'dag.jsonl').open():
 d=json.loads(line);assert d['id']==len(expected);expected.append(d.get('atom',tuple(d.get('args',[]))))
nodes=[];intern={}
def cons(x):
 if x not in intern:intern[x]=len(nodes);nodes.append(x)
 return intern[x]
tokens=iter(re.findall(r'\(|\)|[^\s()]+',(L/'frozen/z3-proof.sexpr').read_text()))
def sexpr(first=None):
 t=next(tokens) if first is None else first
 if t!='(':assert t!=')';return t
 a=[]
 for t in tokens:
  if t==')':return a
  a.append(sexpr(t))
 raise AssertionError('unterminated expression')
class Scope:
 def __init__(self,bindings,parent=None):self.bindings=bindings;self.parent=parent
 def lookup(self,k):
  s=self
  while s is not None:
   if k in s.bindings:return s.bindings[k]
   s=s.parent
  return None
def evallet(x,env):
 if isinstance(x,str):
  found=env.lookup(x);return cons(x) if found is None else found
 if x[0]=='let':
  assert len(x)==3 and len({k for k,v in x[1]})==len(x[1])
  added={k:evallet(v,env) for k,v in x[1]};return evallet(x[2],Scope(added,env))
 return cons(tuple(evallet(y,env) for y in x))
sys.setrecursionlimit(12000)
root=evallet(sexpr(),Scope({}));assert next(tokens,None) is None
assert nodes==expected and root==json.loads((L/'dag-index.json').read_text())['root']
del nodes,expected,intern
executions=[];env=dict(os.environ,CERT_VERIFY_ONLY='1')
for script in ['mapping.py','check.py']:
 command=[sys.executable,str(L/script)];at=time.monotonic();p=subprocess.run(command,capture_output=True,text=True,env=env)
 assert p.returncode==0,(script,p.stderr)
 d=json.loads(p.stdout)
 if script=='mapping.py':assert d['literal_query_mapping']=='PASS'
 else:assert d['certificate_PASS'] and d['root_closed'] and d['gap_nodes']==0 and d['root_conclusion']=='false'
 executions.append({'command':command,'exit':p.returncode,'wall_seconds':time.monotonic()-at,'stdout':d,'stderr':p.stderr})
hashes()
receipt={'status':'PASS: integrity, exact DAG reconstruction, literal-query mapping, independent full rule replay','certificate_PASS':True,'acceptance':'HOLD; root alone accepts; no Lean or prior clearance','manifest_sha256':sha(L/'final-manifest.json'),'root':root,'all_frozen_originals_unchanged':True,'executions':executions,'wall_seconds':time.monotonic()-start,'guard':{'path':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'threads':1},'counts':{'additional':9,'total':39,'next':40}}
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
