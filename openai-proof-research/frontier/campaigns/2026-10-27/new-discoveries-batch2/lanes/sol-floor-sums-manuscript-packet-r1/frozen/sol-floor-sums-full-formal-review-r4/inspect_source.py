from pathlib import Path
import json, hashlib, tarfile, re, collections
L=Path(__file__).resolve().parent
R=L/'replay'
B=L.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for d in iter(lambda:f.read(1048576),b''):h.update(d)
 return h.hexdigest()
refs=[];identities={}
for lane in ['sol-floor-sums-source-formal-r1','sol-floor-sums-certificate-formal-r2']:
 p=B/lane/'source-only.tar.gz';h=sha(p);refs.append(dict(path=str(p),sha256=h));same=[]
 with tarfile.open(p) as t:
  for m in t.getmembers():
   if m.name in ['Reduction.lean','Symmetry.lean','Source.lean','Expansion.lean'] or (m.name.startswith('generated/th_lemma_') and m.name.endswith('.lean')):
    assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==sha(R/m.name),m.name;same.append(m.name)
 assert sha(p)==h
 identities[lane]=same
(L/'immutable-references.json').write_text(json.dumps(refs,indent=2))
mods=json.loads((R/'replay-modules.json').read_text());texts={m:(R/(m.replace('.','/')+'.lean')).read_text() for m in mods}
for m,s in texts.items():
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial)\b',s),m
 assert not re.search(r'run_cmd|elab |initialize|implemented_by|extern|set_option\s+(?:warningAsError\s+false|debug.skipKernelTC|trustLevel)',s),m
seen=set();defs={};ite=[]
for m in ['SemBase']+[f'Sem{i:03}' for i in range(68)]:
 for line in texts[m].splitlines():
  if line.startswith('def e'):
   q=re.fullmatch(r'def (e\d+) \(_v : Vars\) : (ℤ|Prop) := (.+)',line);assert q,line
   n,ty,body=q.groups();assert n not in seen
   assert set(re.findall(r'\b(e\d+)\b',body))<=seen,(n,'forward/free semantic reference')
   defs[n]=(ty,body);seen.add(n)
   if 'if ' in body:assert ty=='ℤ';ite.append(n)
assert defs['e7489']==('Prop','False')
inv=json.loads((L/'frozen/assembly-inventory.json').read_text());found={}
for m,s in texts.items():
 for q in re.finditer(r'^theorem n(\d+) ([^\n]+) := by$',s,re.M):
  n=int(q[1]);assert n not in found;found[n]=(m,q[2])
assert set(found)=={d['node'] for d in inv}
for d in inv:
 m,ty=found[d['node']];assert m==d['module'] or d['module']=='Dag168' and m.startswith('parts.Dag168_'),(d,m);assert set(map(int,re.findall(r'\(h(\d+) :',ty)))==set(d['hyps']),(d,ty);assert ty.endswith(': (e'+str(d['conclusion'])+' _v)'),(d,ty)
assert not inv[-1]['hyps']
selected=[]
for m in json.loads((R/'audit-modules.json').read_text()):
 s=(R/(m+'.lean')).read_text();q=re.search(r'\| some i => if (\[.*\])\.contains',s);selected+=json.loads(q[1]);assert 'env.constants.toList.filterMap' in s and '#check $(mkIdent n)' in s and '#print axioms $(mkIdent n)' in s
assert collections.Counter(selected)==collections.Counter(mods)
out=dict(source_modules=len(mods),semantic_definitions=len(defs),integer_ite_definitions=len(ite),acyclic_typed_semantics=True,dag_theorems=len(found),rules=dict(collections.Counter(d['rule'] for d in inv)),root=found[22671],all_residual_binders_match_inventory=True,audit_exact_module_partition=True,source_token_scan='PASS',inherited_byte_identity=identities)
(L/'structural-review.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='inherited_byte_identity'})
