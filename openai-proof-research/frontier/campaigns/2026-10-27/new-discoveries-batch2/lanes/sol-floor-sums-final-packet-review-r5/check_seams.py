from pathlib import Path
from collections import Counter
import hashlib, json, re, zipfile, tarfile
L=Path(__file__).resolve().parent
P=L/'packet'
sha=lambda b:hashlib.sha256(b).hexdigest()
nodes=[json.loads(s) for s in (P/'certificate/dag.jsonl').read_text().splitlines()]
assert len(nodes)==22672
for i,n in enumerate(nodes):
    assert n['id']==i
    assert all(0<=j<i for j in n.get('args',[]))
seen=set();todo=[22671]
while todo:
    i=todo.pop()
    if i in seen:continue
    seen.add(i);todo.extend(nodes[i].get('args',[]))
assert len(seen)==22672
rules={'rewrite','asserted','mp','hypothesis','monotonicity','intro-def','trans','def-axiom','unit-resolution','th-lemma','lemma','apply-def','not-or-elim'}
counts=Counter()
rule_ids=set()
for i in seen:
    a=nodes[i].get('args',[])
    if a and nodes[a[0]].get('atom') in rules:
        counts[nodes[a[0]]['atom']]+=1;rule_ids.add(i)
assert sum(counts.values())==12459 and counts['lemma']==644 and counts['th-lemma']==1329
formal='\n'.join(p.read_text() for p in (P/'formal').rglob('*.lean'))
actual_ids=[int(n) for n in re.findall(r'^theorem n(\d+)\b',formal,re.M)]
assert len(actual_ids)==len(set(actual_ids)) and set(actual_ids)==rule_ids
assert len(re.findall(r'^def e\d+ .* : (?:ℤ|Prop) :=',formal,re.M))==10188
assert formal.count('by_contra hc')==644
assert 'theorem n22671 (_v : Vars) (_q : Query _v)  : (e7489 _v) := by' in formal
assert 'def e7489 (_v : Vars) : Prop := False' in formal
assert 'structure Vars where\n  (m H t a b c d : ℤ)' in formal
assert len(re.findall(r'^theorem canonical_\d+',formal,re.M))==64
assert len(re.findall(r'^theorem clip_\d+',formal,re.M))==64
assert 'theorem literal_endpoint : FloorSums.LiteralEndpoint := FloorSums.endpoint_of_sorted_clamped_bound sorted_clamped_bound' in formal
ar=json.loads((L/'inputs/reviewed-archive-receipt.json').read_text())
assert sha((P/'source-packet.zip').read_bytes())==ar['zip_sha256']==sha((L/'inputs/reviewed-packet/source-packet.zip').read_bytes())
assert sha((P/'source-packet.tar.gz').read_bytes())==ar['tar_sha256']
with zipfile.ZipFile(P/'source-packet.zip') as z,tarfile.open(P/'source-packet.tar.gz') as t:
    m=json.loads(z.read('SOURCE-MANIFEST.json'))
    assert len(z.namelist())==len(set(z.namelist()))==555
    assert set(z.namelist())==set(m)|{'SOURCE-MANIFEST.json'}==set(t.getnames())
    for n in z.namelist():
        b=z.read(n);assert b==t.extractfile(n).read()==(P/n).read_bytes()
        if n in m:assert sha(b)==m[n]
        assert Path(n).suffix not in {'.olean','.ilean','.ir','.pyc','.pdf'} or n.startswith('sources/')
out={'status':'PASS','dag_nodes':len(nodes),'reachable_rules':len(rule_ids),'rule_counts':dict(counts),'all_rule_ids_equal_unique_Lean_node_theorem_ids':True,'typed_semantic_definitions':10188,'actual_discharge_proof_blocks':644,'canonical_bridges':64,'clip_bridges':64,'unconditional_contradiction_and_endpoint_source_headers':True,'zip_and_tar_all_555_members_equal':True,'zip_sha256':ar['zip_sha256'],'tar_sha256':ar['tar_sha256'],'scope':'Independent source/structure and byte checks, not a new Lean replay or proof-body novelty clearance.'}
(L/'evidence/seam-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
