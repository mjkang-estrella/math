import json,pathlib,hashlib,subprocess,sys,re,base64,collections
p=pathlib.Path.cwd()
def sha(f): return hashlib.sha256(f.read_bytes()).hexdigest()
def save(f,d):
 subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),f],input=json.dumps(d,indent=2),text=True,check=True)
order=json.loads((p/"SOURCE-ORDER.json").read_text())
rr=[]
for f in sorted((p/"receipt").glob("*.json")):
 d=json.loads(f.read_text()); assert d["group_members_left"]==[]
 lp=pathlib.Path(d["log"]);assert lp.is_relative_to(p);assert sha(lp)==d["log_sha256"]
 rr.append((f,d))
sources={};oleans={};receipts={}
r5=json.loads((p/"inputs/independent-review-r5/results/FRESH-REPLAY.json").read_text())
for m in order:
 s=sha(p/"src"/(m+".lean"));assert s==sha(p/"inputs/author-src"/(m+".lean"))==r5["sources_after_checkers"][m]
 sources[m]=s;oleans[m]=sha(p/"build"/(m+".olean"))
 for label in ["lean_"+m,"leanchecker_"+m]:
  f,d=next((f,d) for f,d in rr if d["label"]==label)
  assert d["exit"]==0
  if label=="lean_"+m: assert d["source_sha256"]==s
  receipts[label]={"path":str(f.relative_to(p)),"sha256":sha(f),"exit":d["exit"],"log_sha256":d["log_sha256"]}
save("results/FRESH-REPLAY.json",{"modules":order,"sources":sources,"postchecker_oleans":oleans,"receipts":receipts,"strict":39,"checker":39,"source_equality":"author-src and r5 postchecker hashes; each compile receipt also records same source hash","empty_build":"precompile_pins receipt","pins_before_first_compiler":True,"precompile_separate_source_equality_assertion":False})
manifest=json.loads((p/"inputs/independent-review-r5/SHA256-MANIFEST.json").read_text())
missing=[];bad=[]
for f,h in manifest["files"].items():
 rel=pathlib.PurePath(f);assert not rel.is_absolute() and ".." not in rel.parts
 path=p/"inputs/independent-review-r5"/f
 if not path.exists(): missing.append(f)
 elif sha(path)!=h: bad.append(f)
assert not bad and not missing,(missing,bad)
dag=json.loads((p/"inputs/independent-review-r5/audit/RECOMPUTED-DAG.json").read_text())
def closure(root,nodes):
 seen=set();todo=[root]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(nodes[n]["deps"])
 return seen
for root,ns in dag["closures"].items(): assert closure(root,dag["body_nodes"])==set(ns)
meta=json.loads((p/"audit/METADATA.json").read_text())
nodes={n["name"]:n for n in meta["nodes"] if n["scope"]=="production"}
cl=closure("CMDRR.universalExistsFiveThree_negation",nodes)
assert set(dag["closures"]["CMDRR.universalExistsFiveThree_negation"])<=cl
assert all(set(n["deps"])<=nodes.keys() for n in nodes.values())
scopes={}
for scope in ["production","auxiliary"]:
 ns=[n for n in meta["nodes"] if n["scope"]==scope]
 scopes[scope]={"roots":len(meta["roots"][scope]),"closure":len(ns),"kinds":dict(collections.Counter(n["kind"] for n in ns)),"axioms":[n["name"] for n in ns if n["kind"]=="axiom"],"unsafe_partial":[n["name"] for n in ns if n["unsafe"] or n["partial"]],"runtime_annotations":[n for n in ns if n["extern"] or n["implementedBy"] or n["csimp"]],"bodyless":[n["name"] for n in ns if not n["has_body"]]}
save("audit/METADATA-SUMMARY.json",scopes)
save("audit/VERIFIED-EVIDENCE.json",{"r5_manifest_files":len(manifest["files"]),"mismatches":[],"r5_15_closures_recomputed":True,"old_endpoint_counts":dag["endpoint_counts"],"new_endpoint_with_structural_edges":len(cl),"old_endpoint_subset_new":True,"all_completed_groups_empty":True,"new_endpoint_nodes":sorted(cl)})
pr=json.loads((p/"inputs/source/literal-provenance.json").read_text())
t=next(x for x in pr if x["id"]==326555);raw=base64.b64decode(t["raw_base64"])
assert hashlib.sha256(raw).hexdigest()==t["raw_sha256"]
literal=json.loads((p/"inputs/source/literal326555.jsonl").read_text())
orig=next(json.loads(l) for l in (p/"inputs/source/original-twenty.jsonl").read_text().splitlines() if json.loads(l)["mathdb_id"]==326555)
assert json.loads(raw)==t["object"]==literal==orig
assert hashlib.sha256(literal["statement"].encode()).hexdigest()==t["decoded_statement_sha256"]
assert hashlib.sha256(base64.b64decode(t["raw_statement_token_base64"])).hexdigest()==t["raw_statement_token_sha256"]
save("results/TARGET-PROVENANCE.json",{"id":326555,"object_equal_all4":True,"raw_sha256":t["raw_sha256"],"statement_sha256":t["decoded_statement_sha256"],"original20_count":20,"source_line":t["line"],"chunk_sha256_claim":t["chunk_sha256"],"embedded_chunk_not_read":True})
print("VERIFIED",len(manifest["files"]),"r5 files; fresh39 strict/checker;15 closures; endpoint",len(cl))
print("SUMMARY",json.dumps({s:{k:v for k,v in d.items() if k not in ["bodyless","runtime_annotations"]} for s,d in scopes.items()}))
print("r5 controls")
for f in sorted((p/"inputs/independent-review-r5/receipt").glob("*control*.json")):
 d=json.loads(f.read_text());print(f.name,d["exit"],d["group_members_left"])

